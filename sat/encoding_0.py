from z3 import *
from sat_utils import at_most_one, exactly_one, UnsatError, Vlsi_sat_abstract


class Vlsi_sat(Vlsi_sat_abstract):
    """Class for solving the VLSI problem in SAT, using the encoding 0.

    It inherits from the class `Vlsi_sat_abstract`.

    The solving procedure is based on the SAT variables 'circuit_i_j_k' and 'coord_i_j_k'.
    See the `__solve` method.

    The optimization procedure is very naive. It simply loops through all the possible solutions, keeping the best one.
    At each iteration, the solver is created and run from scratch, with additional constraints imposing to search for a 
    solution different from the ones already found (the already found solutions are not feasible anymore).
    No incremental solving: at each iteration, the solver is created and run from scratch. 
    See the `__optimize` method.

    This encoding is very basic. In particular, the optimization procedure is too naive. 
    It can't be used in practice, because it is too slow.

    """
    def __solve(self, formulas=[]):
        """Solves the given VLSI instance, using the SAT encoding 0.

        It is an auxiliary method. Its aim is to solve the VLSI instance without performing optimization: any solution is 
        good.

        Parameters
        ----------
        formulas : list of z3.z3.BoolRef, optional
            List of additional constraints to impose, by default []

        Returns
        -------
        coords_sol: list of tuple of int
            List containing the coordX and coordY of the lower-left vertex of each circuit.
            Basically, it represents the positions of the circuits in our solution.
        formula_sol: z3.z3.BoolRef
            Boolean formula containing the solution

        Raises
        ------
        UnsatError
            If the given instance is UNSAT

        Notes
        ------
        The following SAT variables are used.
        - circuit_i_j_k, where 'i' in [0,w-1], 'j' in [0,l_max-1], 'k' in [0,n-1].
          '(i,j)' represent two coordinates of the plate, 'k' represents a circuit.
          circuit_i_j_k is True IIF the circuit 'k' is present in the cell '(i,j)' of the plate.
        - coord_i_j_k, where 'i' in [0,w-1], 'j' in [0,l_max-1], 'k' in [0,n-1].
          '(i,j)' represent two coordinates of the plate, 'k' represents a circuit.
          coord_i_j_k is True IIF the left-bottom corner of the circuit 'k' is put in the cell '(i,j)' of the plate.
        `l_max` is the upper bound of the length of the plate. It is defined as `sum(dimsY)`.

        """
        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

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
        # (MAYBE REDUNDANT?)
        for i in range(w):
            for j in range(l_max):
                s.add(at_most_one(circuits[i][j], name=f'at_most_one_circuit_{i}_{j}'))  
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
                    # In such case, a constraint ensuring that `k` can't be put in `(i,j)` is added.
                    if i+dimsX[k]-1>=w or j+dimsY[k]-1>=l_max:
                        s.add(Not(coords[i][j][k]))  # The left-bottom corner of `k` can't be put in `(i,j)`
                        continue

                    # `k` can be put in `(i,j)`
                    
                    # List of tuples, representing the coordinates of the cells of the plate covered by the circuit
                    covered_positions = [(i+ii,j+jj) for ii in range(dimsX[k]) for jj in range(dimsY[k])]

                    # Formula ensuring that no other circuit is present in the `covered_positions`
                    no_overlapping_circuit_formula = And([Not(circuits[ii][jj][kk]) 
                                                        for (ii,jj) in covered_positions for kk in range(n) if kk!=k])
                    # Formula ensuring that all the `covered_positions` actually contain that circuit `k`
                    all_positions_covered_formula = And([circuits[ii][jj][k] for (ii,jj) in covered_positions])

                    # TODO: put negation of all circuits[ii][jj][kk] related to wrong positions? 
                    
                    # The added constraint is the following implication: if bottom-left corner of `k` is in `(i,j)`, then 
                    # `no_overlapping_circuit_formula` and `all_positions_covered_formula` are both True.
                    # Actually, it is an equivalence, not an implication.
                    s.add(coords[i][j][k] == And(no_overlapping_circuit_formula, all_positions_covered_formula))
                    # (MAYBE THE EQUIVALENCE IS REDUNDANT? AN IMPLICATION WOULD BE ENOUGH?)

        # Check if UNSAT 
        if s.check() != sat:
            raise UnsatError('UNSAT')
        
        # Get the solution
        m = s.model()

        # List containing the coordX and coordY of the bottom-left vertex of each circuit
        coords_sol = [(i, j) for k in range(n) for j in range(l_max) for i in range(w) if m.evaluate(coords[i][j][k])]
        # Boolean formula containing the solution
        formula = And([ (coords[i][j][k] if m.evaluate(coords[i][j][k]) else Not(coords[i][j][k])) 
                    for i in range(w) for j in range(l_max) for k in range(n)])

        return coords_sol, formula


    def __compute_l(self, coords):
        """Computes the length of the plate, given the coordinates of the bottom-left verteces of the circuits

        Parameters
        ----------
        coords : list of tuple of int
            List containing the coordX and the coordY of the bottom-left vertex of each circuit 

        Returns
        -------
        l : int
            Length of the plate
        """

        return max([coords[i][1]+self.dimsY[i] for i in range(self.n)])


    def __optimize(self):
        """Solves the given VLSI instance, using the SAT encoding 0.

        It performs optimization: the best solution is found (if any).
        (If this class is used as a parallel process with a time limit, there is not gurantee of founding the optimal 
        solution, but only the best solution found so far).

        The implementation is based on the usage of the `__solve` method.
        Basically, a loop iterating over all the possible solutions is performed, searching for the best possible solution.
        At each iteration, the solver is created and run from scratch, with additional constraints imposing to search 
        for a solution different from the ones already found (the already found solutions are not feasible anymore).

        No incremental solving: at each iteration, the solver is created and run from scratch.

        Raises
        ------
        UnsatError
            If the given instance is UNSAT

        Notes
        ------
        The solution is communicated to the user through the `results` dictionary, which is shared between the class and the 
        user. 
        Each time a better solution is found, it is injected to the `results` dictionary.
        """
        # List of additional constraints to inject
        formulas = []
        # Boolean flag reprenting if a first solution has already been found
        first_solution = False
        
        # Loop iterating over all the possible solutions, searching for the best one
        while True:
            try:
                # Search for a solution (given the additional constraints in `formulas`)
                coords, formula = self.__solve(formulas=formulas)

                # Append into `formulas` the negation of the returned `formula`, which represents the current solution.
                # In this way, in the next iteration, the same solution is not feasible anymore
                formulas.append(Not(formula))  

                # Length of the plate of the current solution
                l = self.__compute_l(coords)

                # TODO: remove
                # print(l)
                # print(coords)

                # Check if the current solution is the best solution found so far and, if yer, update the current best 
                # solution
                if first_solution or l < self.results['best_l']:
                    first_solution = True
                    self.results['best_coords'] = coords
                    self.results['best_l'] = l

            except UnsatError:  # Found UNSAT: leave the cycle
                break

        # The computation is finished
        self.results['finish'] = True
                
        if not first_solution:  # No solution has been found: UNSAT
            raise UnsatError('UNSAT')        


    def run(self):
        # Code executed by the process when it is runned
        try:
            self.__optimize()
        except UnsatError:
            self.results['unsat'] = True