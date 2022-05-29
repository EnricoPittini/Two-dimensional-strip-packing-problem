from z3 import *
from itertools import combinations

def at_least_one(B):
    return Or(B)
def at_most_one(B, name=""):
    return And( [Not(And(pair[0], pair[1])) for pair in combinations(B, 2)] )
def exactly_one(B, name=''):
    return And(at_least_one(B), at_most_one(B, name=name))

class UnsatError(BaseException):
    pass


def __vlsi_sat(w, n, dimsX, dimsY, formulas=[]):
    s = Solver()
    s.add(And(formulas))
    
    l_max = sum(dimsY)
    
    circuits = [[[Bool(f'circuit_{i}_{j}_{k}') for k in range(n)] for j in range(l_max)] for i in range(w)]
    coords = [[[Bool(f'coord_{i}_{j}_{k}') for k in range(n)] for j in range(l_max)] for i in range(w)]
    
    for i in range(w):
        for j in range(l_max):
            s.add(at_most_one(circuits[i][j], name=f'at_most_one_circuit_{i}_{j}'))  # TODO : redundant?
            s.add(at_most_one(coords[i][j], name=f'at_most_one_coord_{i}_{j}'))
            
    for k in range(n):
        s.add(exactly_one([coords[i][j][k] for i in range(w) for j in range(l_max)], name=f'exactly_one_{k}'))
            
    for k in range(n):
        for i in range(w):
            for j in range(l_max):
                #print(f'k {k} i {i} j {j}')
                if i+dimsX[k]-1>=w or j+dimsY[k]-1>=l_max:
                    s.add(Not(coords[i][j][k]))
                    continue
                right_positions = [(i+ii,j+jj) for ii in range(dimsX[k]) for jj in range(dimsY[k])]
                formula1 = And([Not(circuits[ii][jj][kk]) for (ii,jj) in right_positions for kk in range(n) if kk!=k])
                formula2 = And([circuits[ii][jj][k] for (ii,jj) in right_positions ])
                # TODO: put negation of all circuits[ii][jj][kk] related to wrong positions? 
                s.add(coords[i][j][k] == And(formula1,formula2))
                
    if s.check() != sat:
        raise UnsatError()
    
    m = s.model()

    coords_sol = [(i, j, k) for k in range(n) for j in range(l_max) for i in range(w) if m.evaluate(coords[i][j][k])]
    formula = And([ (coords[i][j][k] if m.evaluate(coords[i][j][k]) else Not(coords[i][j][k])) for i in range(w) for j in range(l_max) for k in range(n)])
    return coords_sol, formula


def __compute_max_l(coords, dimsY, n):
    return max([coords[i][1]+dimsY[i] for i in range(n)])


def vlsi_sat(w, n, dims):
    dimsX = [dims[i][0] for i in range(n)]
    dimsY = [dims[i][1] for i in range(n)]

    formulas = []
    
    first = True
    
    #best_l = sum(dimsY)+1
    
    while True:
        try:
            coords_sol, formula = __vlsi_sat(w, n, dimsX, dimsY, formulas=formulas)
            formulas.append(Not(formula))
            l = __compute_max_l(coords_sol, dimsY, n)
            print(l)
            print(coords_sol)
            if first or l < best_l:
                first = False
                best_coords_sol = coords_sol
                best_l = l
                print(f'best_l {best_l}')
        except UnsatError:
            break
            
    if first:
        return 'Unsat'
    
    return best_coords_sol, best_l              