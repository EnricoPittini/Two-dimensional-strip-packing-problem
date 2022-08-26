import enum
import math
import sys
import numpy as np
import os
import pandas as pd
from time import time
from amplpy import AMPL


def apply_position_and_covering(w, n, dims, ampl, solver, time_limit, use_rotations, cplex_options, gurobi_options):
    start_time = time()
    
    # Fail if the instance is unsatisfiable 
    for d in dims:
        if d[0] > w:
            sys.exit('error = UNSATISFIABLE')

    # Compute minimum l of the plate 
    if use_rotations:
        current_l = sum([d[0]*d[1] for d in dims]) // w
    else:
        current_l = max(max([d[1] for d in dims]), sum([d[0]*d[1] for d in dims]) // w)

    while time() - start_time <= time_limit:
        # Update parameter l for new run of the model
        ampl.param['l'] = current_l

        V, C =_get_valid_positions(dims, n, w, current_l, use_rotations)
        
        ampl.param['nPos'] = C.shape[0]
        ampl.param['nCells'] = C.shape[1]
        ampl.param['C'] = [C[i,j] for i in range(C.shape[0]) for j in range(C.shape[1])]
        
        ampl.param['minV'] = [v[0] for v in V]
        ampl.param['maxV'] = [v[-1] for v in V]
        
        spent_time = time() - start_time 

        if solver == 'cplex':
            ampl.set_option('cplex_options', ' '.join(cplex_options) + f" timelimit={max(time_limit - spent_time, 0)}")
        elif solver == 'cbc':
            ampl.set_option('cbc_options', f" sec={max(time_limit - spent_time, 0)}")
        elif solver == 'gurobi':
            ampl.set_option('gurobi_options', ' '.join(gurobi_options) + f" timelim={max(time_limit - spent_time, 0)}")

        ampl.solve()

        result = ampl.get_value('solve_result')
        if result == 'solved': #or result == 'limit':
            x = ampl.get_data('x').to_pandas().x.values
            if use_rotations:
                final_positions = [x[c*C.shape[0] : (c+1)*C.shape[0]] for c in range(n)]
                final_positions = [np.argmax(x) + 1 - V[i][0] if 1 in x else None for i, x in enumerate(final_positions)]
                
                final_positions_r = [x[c*C.shape[0] : (c+1)*C.shape[0]] for c in range(n,2*n)]
                final_positions_r = [np.argmax(x) + 1 - V[i+n][0] if 1 in x else None 
                                     for i, x in enumerate(final_positions_r)]

                coordsX = []
                coordsY = []
                for i in range(n):
                    r = final_positions[i] is None
                    p = final_positions_r[i] if r else final_positions[i]
                    w_i = dims[i][1] if r else dims[i][0]
                    h_i = dims[i][0] if r else dims[i][1]
                    coordsX.append(p % ((w - w_i)+1))
                    coordsY.append(current_l - p // ((w - w_i) + 1) - h_i )

                dims = [(dims[i][0], dims[i][1]) if p is not None else (dims[i][1], dims[i][0]) 
                        for i, p in enumerate(final_positions)]

            else:
                final_positions = [x[c*C.shape[0] : (c+1)*C.shape[0]] for c in range(n)]
                final_positions = [np.argmax(x) + 1 - V[i][0] for i, x in enumerate(final_positions)]

                coordsX = [p % ((w - dims[i][0])+1) for i, p in enumerate(final_positions)]
                coordsY = [current_l - p // ((w - dims[i][0])+1) - dims[i][1] 
                        for i, p in enumerate(final_positions)]     
            solving_time =  time() - start_time      
            if solving_time <= time_limit:
                return dims, coordsX, coordsY, current_l, solving_time
            else:
                # If time has been exceeded cast the solution as UNKNOWN
                return None, None, None, None, None
        current_l += 1
    # If no solution has been found the process finishes with an unknown result.
    return None, None, None, None, None

def _get_valid_positions(dims, n, w, current_l, use_rotations):
    V = []

    position = 1
    for c in range(n):
        num_positions = (w - dims[c][0] + 1)*(current_l - dims[c][1] + 1)
        V.append(np.arange(position, position + num_positions))
        position += num_positions
    if use_rotations:
        for c in range(n):
            num_positions = (w - dims[c][1] + 1)*(current_l - dims[c][0] + 1)
            V.append(np.arange(position, position + num_positions))
            position += num_positions
        
    C = np.zeros((position-1, w*current_l), dtype='b')
    
    for c in range(n):
        for i, p in enumerate(V[c]):
            pX = i // (w - dims[c][0] + 1)
            pY = i % (w - dims[c][0] + 1)
            cells = [(pX+j)*w + pY + 1 + k for j in range(dims[c][1]) for k in range(dims[c][0])]

            for cell in cells:
                C[p-1, cell-1] = 1
    if use_rotations:
        for c in range(n):
            for i, p in enumerate(V[c+n]):
                pX = i // (w - dims[c][1] + 1)
                pY = i % (w - dims[c][1] + 1)
                cells = [(pX+j)*w + pY + 1 + k for j in range(dims[c][0]) for k in range(dims[c][1])]

                for cell in cells:
                    C[p-1, cell-1] = 1
            
    return V, C
