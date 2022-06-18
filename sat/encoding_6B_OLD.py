from math import ceil
from socket import timeout
import time
from z3 import *
from sat_utils import at_least_one, at_most_one, exactly_one, UnsatError, compute_l

# TODO: put better bounds on w and l_max


def __vlsi_sat(w, n, dimsX, dimsY, w_min, h_min, l_min, l_max):

    s = Solver()  # Solver instance
    
    # Upper bound of the length of the plate, if not explicitely given in input
    # l_max = sum(dimsY)
    
    # List of lists of lists, containing the 'circuits' boolean variables: variables 'circuit_i_j_k'
    circuits = [[[Bool(f'circuit_{i}_{j}_{k}') for k in range(n)] for j in range(l_max)] for i in range(w)]
    # List of lists of lists, containing the 'coords' boolean variables: variables 'coord_i_j_k'
    # coords = [[[Bool(f'coord_{i}_{j}_{k}') for k in range(n)] for j in range(l_max-h_min+1)] for i in range(w-w_min+1)]
    # List of lists of lists, containing the 'lengths' boolean variables: variables 'length_k_l'
    lengths = [Bool(f'length_{l}') for l in range(l_max-l_min+1)]
    
    # Constraint: in each cell '(i,j)' of the plate at most one circuit is present.
    # This reflects both on `circuits` and on `coords`.
    for i in range(w):
        for j in range(l_max):
            s.add(at_most_one(circuits[i][j], name=f'at_most_one_circuit_{i}_{j}'))  # TODO : redundant?
            #s.add(at_most_one(coords[i][j], name=f'at_most_one_coord_{i}_{j}'))
            
    # Constraint: the left-bottom corner of each circuit 'k' must be present exactly one time across the plate
    #for k in range(n):
    #    s.add(exactly_one([coords[i][j][k] for i in range(w-w_min+1) for j in range(l_max-h_min+1)], name=f'exactly_one_{k}'))

    print('CUCU')  # TODO: remove

    # Constraint: for each circuit 'k' and for each cell '(i,j)' of the plate, if that cell contains the left-bottom corner 
    # of 'k', then all the cells covered by the circuit 'k' must contain only that circuit and no other circuits.      
    for k in range(n):
        formulas = []
        for i in range(w):
            for j in range(l_max):
                # Current iteration: circuit `k` and cell `(i,j)` of the plate.
                # Now the constraint about putting the left-bottom corner of `k` in `(i,j)` is ensured.

                # Case in which `k` can't be put in `(i,j)`, because it goes out of the bounds of the plate.
                # In such case, a constraint ensuring that `k` can't be put in `(i,j)` is esnured.
                if i+dimsX[k]-1>=w or j+dimsY[k]-1>=l_max:
                #    s.add(Not(coords[i][j][k]))  # The left-bottom corner of `k` can't be put in `(i,j)`
                    #covered_positions = [(i+ii,j+jj) for ii in range(1,dimsX[k]) for jj in range(1,dimsY[k])
                                                     #if i+ii-1<w and j+jj- ]
                    #s.add(And([Not(circuits[ii][jj][k]) for (ii,jj) in covered_positions]))
                    continue
                
                # List of tuples, representing the coordinates of the cells of the plate covered by the circuit
                covered_positions = [(i+ii,j+jj) for ii in range(dimsX[k]) for jj in range(dimsY[k])]
                non_covered_positions = list(set([(ii,jj) for ii in range(w) for jj in range(l_max)]) 
                                             - set(covered_positions))
                #non_covered_positions = [(ii,jj) for ii in range(w) for jj in range(l_max) if (ii,jj) not in covered_positions]
                #print('cov', covered_positions)
                #print('non-cov', sorted(non_covered_positions))

                # Formula ensuring that no other circuit is present in the `covered_positions`
                #no_overlapping_circuit_formula = And([Not(circuits[ii][jj][kk]) 
                #                                      for (ii,jj) in covered_positions for kk in range(n) if kk!=k])
                # Formula ensuring that all the `covered_positions` actually contain that circuit `k`
                all_positions_covered_formula = And([circuits[ii][jj][k] for (ii,jj) in covered_positions])                
                all_positions_not_covered_formula = And([Not(circuits[ii][jj][k]) for (ii,jj) in non_covered_positions])
                formulas.append(And(all_positions_covered_formula,all_positions_not_covered_formula))
                #formulas.append(all_positions_covered_formula)
                
                # TODO: put negation of all circuits[ii][jj][k] related to wrong positions? 
                # The added constraint is the following implication: if left-bottom corner of `k` in `(i,j)`, then 
                # `no_overlapping_circuit_formula` and `all_positions_covered_formula`.
                # Actually, it is not an implication, nut an equivalence.
                #s.add(coords[i][j][k] == And(no_overlapping_circuit_formula,all_positions_covered_formula))

                # Formula ensuring that all the lengths up to `j+dimsY[k]-1` are used by the circuit `k`
                #used_lengths_formula = And([lengths[k][l] for l in range(j+dimsY[k]-l_min+1)])
                # Formula ensuring that all the lengths from `j+dimsY[k]` are not used by the circuit `k`
                #non_used_lengths_formula = And([Not(lengths[k][l]) for l in range(j+dimsY[k]-l_min+1, l_max-l_min+1)])
                # The added constraint is the following implication: if left-bottom corner of `k` in `(i,j)`, then 
                # `used_lengths_formula` and `non_used_lengths_formula`.
                #s.add(Implies(coords[i][j][k], And(used_lengths_formula, non_used_lengths_formula)))
                #formulas.append(And(all_positions_covered_formula,all_positions_not_covered_formula,used_lengths_formula,
                #                   non_used_lengths_formula))
        s.add(exactly_one(formulas, name=f'exactly_one_{k}'))
        #s.add(Or(formulas))
        #print()

    print('HERE')  # TODO: remove

    s.add(exactly_one(lengths))
    for l in range(l_max-l_min+1):
        l_index = l+l_min-1
        at_least_one_circuit_of_that_length_formula = at_least_one([circuits[i][l_index][k] for i in range(w) for k in range(n)])
        no_above_circuits_formula = And([Not(circuits[i][j][k]) for i in range(w) for j in range(l_index+1, l_max) for k in range(n)])
        s.add(lengths[l] == And(at_least_one_circuit_of_that_length_formula,no_above_circuits_formula))

    # Check if UNSAT 
    if s.check() != sat:
        raise UnsatError('UNSAT')
        
    """m = s.model()
    
    coords = []
    for k in range(n):
        coord = min([(i,j) for i in range(w-w_min+1) for j in range(l_max-h_min+1) if m.evaluate(circuits[i][j][k])])
        print(coord)
        coords.append(coord)"""
        
    return s, circuits, lengths


def process_solver_instance(s, circuits, lengths, w, n, w_min, h_min, l_min, l_max, current_best_l):
    """Processes the given solver instance.

    Two operations are performed:
        - the new solution is extracted from the given solver;
        - additional constraints are injected into the solver, in order to find the next best solution (incremental solving).

    Parameters
    ----------
    s : z3.z3.Solver
        Solver instance
    coords : list of list of list of z3.z3.BoolRef
        Boolean variables 'coord_i_j_k'.
    lengths : list of list of z3.z3.BoolRef
        Boolean variables 'length_k_l'.
    w : int
        Width of the plate
    n : int
        Number of circuits
    l_max : int
        Upper bound of the length of the plate
    current_best_l : int
        Current best length of the plate (found so far)

    Returns
    -------
    coords_sol : list of tuple of int
        Coordinates of the left-bottom corner of the circuits of the new solution
    l : int
        Length of the plate of the new solution
    """
    if not current_best_l:
        current_best_l = l_max+1
    
    # Get the solution
    m = s.model()
    
    coords_sol = []    
    for k in range(n):
        coord = min([(i,j) for i in range(w) for j in range(l_max) if m.evaluate(circuits[i][j][k])])
        # print(coord)
        coords_sol.append(coord)
    #print(coords_sol)

    # List containing the coordX and coordY of the lower-left vertex of each circuit
    # coords_sol = [(i, j) for k in range(n) for j in range(l_max-h_min+1) for i in range(w-w_min+1) if m.evaluate(coords[i][j][k])]
    # Boolean formula containing the solution
    # formula = And([ (coords[i][j][k] if m.evaluate(coords[i][j][k]) else Not(coords[i][j][k])) 
                  #for i in range(w-w_min+1) for j in range(l_max-h_min+1) for k in range(n)])

    # Length of the plate
    #print(type(lengths[0][0]))
    #print(lengths[0][0])
    l = max([l for l in range(l_max-l_min+1) if m.evaluate(lengths[l])])+l_min-1+1
    
    # Add into the solver the negation of the returned `formula`, which represents the current solution.
    # In this way, in the next iteration, the same solution is not feasible anymore
    #s.add(Not(formula))  

    # Add into the solver a constraint ensuring that a solution which has a length bigger or equal than `l-2` is not feasible
    # anymore: in this way, the next found solution, if any, is for sure better than the previous one.
    # This is implemented by ensuring that all the variables 'lengths_k_ll' with 'll' from 'l-1' (included) to 
    # 'current_best_l-1' (exclued) are False.
    #s.add(And([Not(lengths[ll]) for ll in range(l-1,current_best_l-1)]))
    s.add(Or([lengths[ll] for ll in range(l-1-l_min+1)]))
    
    return coords_sol, l


def vlsi_sat(w, n, dims, timeout=300):
    """Solves the given VLSI instance using a SAT encoding.

    It performs optimization: the best solution is returned (if any).
    More precisely, the best solution found strictly within the time limit is returned (if any).

    The implementation is based on the usage of the `__vlsi_sat` auxiliary function.
    Basically, a loop iterating over all the possible solutions is performed, searching for the best possible solution.

    Parameters
    ----------
    w : int
        The width of the plate
    n : int
        The number of circuits
    dims : list of tuple of int
        Dims X and Y (i.e. width and height) of the circuits
    timeout : int, optional
        Time limit in seconds for executing the SAT solver, by default 300 (i.e. 5 minutes)

    Returns
    -------
    best_coords: list of tuples of int
        List containing the coordX and coordY of the lower-left vertex of each circuit in the best solution
    best_l: int
        Length of the plate in the best solution

    Raises
    ------
    UnsatError
        If the given instance is UNSAT in the specified time limit.

    Notes
    ------
    Remarks about the time limit.
    It may happen that the user has to wait a bit longer than the specified time limit. (Basically, for recognizing the 
    exceeding of the time limit, the solver has to terminate).
    However, it is guaranteed that the returned solution has been found strictly within the time limit.
    """
    start_time = time.time()

    # Split `dims` into `dimsX` and `dimsY`
    dimsX = [dims[i][0] for i in range(n)]
    dimsY = [dims[i][1] for i in range(n)]

    areas = [dimsX[i]*dimsY[i] for i in range(n)]  # The areas of the circuits
    A_tot = sum(areas)  # The overall area of all the given circuits
    h_min = min(dimsY)  # The minimum height of a circuit
    h_max = max(dimsY)  # The maximum height of a circuit
    w_min = min(dimsX)  # The minimum width of a circuit
    w_max = max(dimsX)  # The maximum width of a circuit
    l_min = max([h_max, A_tot // w])  # The lower bound for the length
    min_rects_per_row = w // w_max  # Minimum number of circuits per row
    max_rects_per_col = ceil(n / max([1, min_rects_per_row]))  # Maximum number of circuits per column
    # The upper bound for the length
    #l_max =  sum(sorted(dimsY)[n-max_rects_per_col:])
    sorted_dimsY = sorted(dimsY, reverse=True)
    l_max = sum([sorted_dimsY[i] for i in range(n) if i % min_rects_per_row == 0])

    """# l_max = sum(dimsY)
    # Define the upper bound for the length of the plate
    w_max = max(dimsX)
    min_rects_per_row = w // w_max  # Minimum number of circuits per row
    max_rects_per_col = ceil(n / max([1, min_rects_per_row]))  # Maximum number of circuits per column
    # The upper bound for the length
    #l_max =  sum(sorted(dimsY)[n-max_rects_per_col:])
    sorted_dimsY = sorted(dimsY, reverse=True)
    l_max = sum([sorted_dimsY[i] for i in range(n) if i % min_rects_per_row == 0])"""
    
    # Search for a first solution 
    s, circuits, lengths = __vlsi_sat(w, n, dimsX, dimsY, w_min, h_min, l_min, l_max)
    best_coords, best_l = process_solver_instance(s, circuits, lengths, w, n, w_min, h_min, l_min, l_max, current_best_l=None)

    solving_time = time.time() - start_time
    if solving_time>timeout:  # The first solution has been found after the time out: no found solution
        raise UnsatError('UNSAT')

    # A first solution has been found

    print(best_coords)
    print(best_l)
       
    # Loop iterating over all the possible solutions, searching for the best one
    while True:
        if s.check()!=sat:  # No more solutions: break the cycle
            break

        # A new solution has been found

        solving_time = time.time() - start_time
        if solving_time>timeout:  # The new solution has been found after the time out: no valid solution. Break the cycle
            break

        # New valid solution

        # Get the new valid solution and inject the new constraints into the solver
        best_coords, best_l = process_solver_instance(s, circuits, lengths, w, n, w_min, h_min, l_min, l_max, best_l)        
        print(best_coords)
        print(best_l)
    
    # Return the best found solution. 
    # (For sure one solution has been found, however it can be non-optimal due to the timeout).
    return best_coords, best_l            