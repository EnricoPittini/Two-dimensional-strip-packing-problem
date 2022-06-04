import time
from z3 import *
from sat_utils import at_least_one, at_most_one, exactly_one, UnsatError, compute_l
import multiprocessing


def _vlsi_sat(w, n, dimsX, dimsY, formulas=[]):
    """Solves the given VLSI instance using a SAT encoding.

    It is an auxiliary function. Its aim is to solve the VLSI instance without performing optimization: any solution is good.

    Parameters
    ----------
    w : int
        The width of the plate
    n : int
        The number of circuits
    dimsX : list of int
        Dims X (i.e. width) of the circuits
    dimsY : list of int
        Dims Y (i.e. height) of the circuits
    formulas : list of z3.z3.BoolRef, optional
        List of additional constraints to impose, by default []

    Returns
    -------
    coords_sol: list of tuple of int
        List containing the coordX and coordY of the lower-left vertex of each circuit
    formula_sol: z3.z3.BoolRef
        Boolean formula containing the solution

    Raises
    ------
    UnsatError
        If the given instance is UNSAT

    Notes
    ------
    The following boolean variables are used
    - circuit_i_j_k, where 'i' in [0,w], 'j' in [0,l_max], 'k' in [0,n]. ('l_max' is the upper bound of the length of the 
      plate).
      '(i,j)' represent two coordinates of the plate, 'k' represents a circuit.
       circuit_i_j_k is True IIF the circuit 'k' is present in the cell '(i,j)' of the plate.
    - coord_i_j_k, where 'i' in [0,w], 'j' in [0,l_max], 'k' in [0,n].
      '(i,j)' represent two coordinates of the plate, 'k' represents a circuit.
       coord_i_j_k is True IIF the left-bottom corner of the circuit 'k' is put in the cell '(i,j)' of the plate.
    """
    s = Solver()  # Solver instance
    s.add(And(formulas))  # Add the given optional formulas
    
    # Upper bound of the length of the plate
    l_max = sum(dimsY)
    
    # List of lists of lists, containing the 'circuits' boolean variables: variables 'circuit_i_j_k'
    circuits = [[[Bool(f'circuit_{i}_{j}_{k}') for k in range(n)] for j in range(l_max)] for i in range(w)]
    # List of lists of lists, containing the 'coords' boolean variables: variables 'coord_i_j_k'
    coords = [[[Bool(f'coord_{i}_{j}_{k}') for k in range(n)] for j in range(l_max)] for i in range(w)]
    
    # Constraint: in each cell '(i,j)' of the plate at most one circuit is present.
    # This reflects both on `circuits` and on `coords`.
    for i in range(w):
        for j in range(l_max):
            s.add(at_most_one(circuits[i][j], name=f'at_most_one_circuit_{i}_{j}'))  # TODO : redundant?
            s.add(at_most_one(coords[i][j], name=f'at_most_one_coord_{i}_{j}'))
            
    # Constraint: the left-bottom corner of each circuit 'k' must be present exactly one time across the plate
    for k in range(n):
        s.add(exactly_one([coords[i][j][k] for i in range(w) for j in range(l_max)], name=f'exactly_one_{k}'))

    # Constraint: for each circuit 'k' and for each cell '(i,j)' of the plate, if that cell contains the left-bottom corner 
    # of 'k', then all the cells covered by the circuit 'k' must contain only that circuit and no other circuits.      
    for k in range(n):
        for i in range(w):
            for j in range(l_max):
                # Current iteration: circuit `k` and cell `(i,j)` of the plate.
                # Now the constraint about putting the left-bottom corner of `k` in `(i,j)` is ensured.

                # Case in which `k` can't be put in `(i,j)`, because it goes out of the bounds of the plate.
                # In such case, a constraint ensuring that `k` can't be put in `(i,j)` is esnured.
                if i+dimsX[k]-1>=w or j+dimsY[k]-1>=l_max:
                    s.add(Not(coords[i][j][k]))  # The left-bottom corner of `k` can't be put in `(i,j)`
                    continue
                
                # List of tuples, representing the coordinates of the cells of the plate covered by the circuit
                covered_positions = [(i+ii,j+jj) for ii in range(dimsX[k]) for jj in range(dimsY[k])]

                # Formula ensuring that no other circuit is present in the `covered_positions`
                no_overlapping_circuit_formula = And([Not(circuits[ii][jj][kk]) 
                                                      for (ii,jj) in covered_positions for kk in range(n) if kk!=k])
                # Formula ensuring that all the `covered_positions` actually contain that circuit `k`
                all_positions_covered_formula = And([circuits[ii][jj][k] for (ii,jj) in covered_positions])

                # TODO: put negation of all circuits[ii][jj][kk] related to wrong positions? 
                # The added constraint is the following implication: if left-bottom corner of `k` in `(i,j)`, then 
                # `no_overlapping_circuit_formula` and `all_positions_covered_formula`
                s.add(coords[i][j][k] == And(no_overlapping_circuit_formula,all_positions_covered_formula))

    # Check if UNSAT 
    if s.check() != sat:
        raise UnsatError('UNSAT')
    
    # Get the solution
    m = s.model()

    # List containing the coordX and coordY of the lower-left vertex of each circuit
    coords_sol = [(i, j) for k in range(n) for j in range(l_max) for i in range(w) if m.evaluate(coords[i][j][k])]
    # Boolean formula containing the solution
    formula = And([ (coords[i][j][k] if m.evaluate(coords[i][j][k]) else Not(coords[i][j][k])) 
                  for i in range(w) for j in range(l_max) for k in range(n)])

    return coords_sol, formula


def vlsi_sat(w, n, dims, timeout=300):
    manager = multiprocessing.Manager()
    results = manager.dict()
    p = Vlsi_sat(w, n, dims, results)
    p.start()

    p.join(timeout)

    if p.is_alive():
        p.terminate()
        p.join()   

    return results['best_coords'], results['best_l'], results['finish']     


class Vlsi_sat(multiprocessing.Process):
    def __init__(self, w, n, dims, results):
        super().__init__()
        self.w = w
        self.n = n 
        self.dimsX = [dims[i][0] for i in range(n)]
        self.dimsY = [dims[i][1] for i in range(n)]
        self.results = results
        self.results['best_coords'] = None
        self.results['best_l'] = None
        self.results['finish'] = False
    def run(self):
        # List of additional constraints to inject
        formulas = []
        # Boolean flag reprenting if the first solution has not been found yet
        first = True
        
        # Loop iterating over all the possible solutions, searching for the best one
        while True:
            try:
                # Search for a solution (given the additional constraints in `formulas`)
                coords, formula = _vlsi_sat(self.w, self.n, self.dimsX, self.dimsY, formulas=formulas)

                # Append into `formulas` the negation of the returned `formula`, which represents the current solution.
                # In this way, in the next iteration, the same solution is not feasible anymore
                formulas.append(Not(formula))  

                # Length of the plate of the current solution
                l = compute_l(coords, self.dimsY, self.n)

                # TODO: remove
                print(l)
                print(coords)

                # Check if the current solution is the best solution found so far
                if first or l < self.results['best_l']:
                    first = False
                    self.results['best_coords'] = coords
                    self.results['best_l'] = l
                    # print(self.best_coords, self.best_l)
                    # print(f'best_l {best_l}') # TODO: remove

            except UnsatError:  # Found UNSAT: leave the cycle
                break
                
        if first:  # No solution has been found: UNSAT
            raise UnsatError('UNSAT')

        self.results['finish'] = True
        
        # Return the best found solution. 
        # (For sure one solution has been found, however it can be non-optimal due to the timeout).
        # return best_coords, best_l  