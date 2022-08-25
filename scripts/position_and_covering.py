import math
import sys
import numpy as np
import os
import pandas as pd
from time import time
from amplpy import AMPL


def apply_position_and_covering(w, n, dims, ampl, model, solver, time_limit, use_symmetries, use_dual, cplex_options, gurobi_options):
    start_time = time()
    
    # Fail if the instance is unsatisfiable 
    for d in dims:
        if int(d[0]) > int(w):
            sys.exit('error = UNSATISFIABLE')

    # Compute minimum l of the plate 
    current_l = max(max([int(d[1]) for d in dims]), sum([int(d[0])*int(d[1]) for d in dims]) // int(w))

    while time() - start_time <= time_limit:
        # Update parameter l for new run of the model
        ampl.param['l'] = current_l

        V, C =_get_valid_positions(dims, n, w, current_l)
        
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
        if result == 'solved' or result == 'limit':
            x = ampl.get_data('x').to_pandas().x.values

            final_positions = [x[c*C.shape[0] : (c+1)*C.shape[0]] for c in range(int(n))]
            final_positions = [np.argmax(x) + 1 - V[i][0] for i, x in enumerate(final_positions)]

            coordsX = [(p) % ((int(w) - int(dims[i][0]))+1) for i, p in enumerate(final_positions)]
            coordsY = [current_l - (p) // ((int(w) - int(dims[i][0]))+1) - int(dims[i][1]) 
                       for i, p in enumerate(final_positions)]            

            return coordsX, coordsY, current_l, time() - start_time

        current_l += 1
    return None, None, None, None


def _read_dat_file(w, n, dims, ampl):
    """Create and read `.dat` file of an instance and read it in order to execute the `AMPL` model on it.

    Parameters
    ----------
    w : int
        The width of the plate
    n : int
        The number of circuits
    dims : list of tuple of int
        Dims X and Y (i.e. width and height) of the circuits
    ampl : AMPL
        An AMPL translator
    """
    data_file_path = 'data.dat'

    # Create `.dat` data file with `AMPL` required format.
    with open(data_file_path,'w') as fp:
        fp.write('data;\n')
        fp.write(f'param n := {n};\n')
        fp.write(f'param w := {w};\n')
        fp.write('param: dimsX dimsY :=\n')
        for i, dim in enumerate(dims):
            fp.write(f'{i+1}\t\t{dim[0]}\t\t{dim[1]}\n')
        fp.write(';')
    ampl.read_data(data_file_path)

    # Delete `.dat` data file.
    if os.path.exists(data_file_path):
        os.remove(data_file_path)

def _get_valid_positions(dims, n, w, current_l):
    V = []

    position = 1
    for c in range(int(n)):
        num_positions = (int(w) - int(dims[c][0]) + 1)*(current_l - int(dims[c][1]) + 1)
        V.append(np.arange(position, position + num_positions))
        position += num_positions

    C = np.zeros((position-1, int(w)*int(current_l)), dtype='b')
    
    for c in range(int(n)):
        for i, p in enumerate(V[c]):
            pX = i // (int(w) - int(dims[c][0]) + 1)
            pY = i % (int(w) - int(dims[c][0]) + 1)
            cells = [(pX+j)*int(w) + pY + 1 + k for j in range(int(dims[c][1])) for k in range(int(dims[c][0]))]

            for cell in cells:
                C[p-1, cell-1] = 1

    return V, C
