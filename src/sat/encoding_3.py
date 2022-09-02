from z3 import *
from sat_utils import at_most_one, exactly_one, UnsatError, Vlsi_sat_abstract


class Vlsi_sat(Vlsi_sat_abstract):
    """Class for solving the VLSI problem in SAT, using the encoding 3.

    It inherits from the class `Vlsi_sat_abstract`.

    Both the solving and the optimization are very similar to the encoding 2.
    The only difference is about the bounds of the variables. 

    Better bounds for all the SAT variables: 'circuit_i_j_k', 'coord_i_j_k' and 'length_k_l'.
        1. 'circuit_i_j_k': i in [0,w-w_min], j in [0,l_max-h_min], k in [0,n-1]
        2. 'coord_i_j_k': i in [0,w-w_min], j in [0,l_max-h_min], k in [0,n-1]
        3. 'length_k_l': k in [0,n-1], l in [0,l_max-l_min]
            For going from an index 'l' of 'length_k_l' to the actual length: l+l_min.
            For going from an actual length 'l' to an index of 'length_k_l': l-l_min.
                Example. l_min=3, l_max=9.
                For each circuit 'k', the variables 'length_k_l' are: 
                            - length_k_0 (corresponding to the actual length 3)
                            - length_k_1 (corresponding to the actual length 4)
                            - length_k_2 (corresponding to the actual length 5)
                            ...
                            - length_k_6 (corresponding to the actual length 9)

    """
    def __solve(self, w_min, h_min, l_min, l_max):
        """Solves the given VLSI instance, using the SAT encoding 3.

        It is an auxiliary method. Its aim is to solve the VLSI instance without performing optimization: any solution is 
        good.

        Parameters
        ----------
        w_min : int
            Minimum width of a circuit
        h_min : int
            Minimum height of a circuit
        l_min : int
            Lower bound of the length of the plate
        l_max : int
            Upper bound of the length of the plate

        Returns
        -------
        s: z3.z3.Solver
            The solver instance
        coords : list of list of list of z3.z3.BoolRef
            Boolean variables 'coord_i_j_k'.
            See `Notes`.
        lengths : list of list of z3.z3.BoolRef
            Boolean variables 'length_k_l'.
            See `Notes`.

        Notes
        ------
        The following boolean variables are used
        - circuit_i_j_k, where 'i' in [0,w-w_min], 'j' in [0,l_max-h_min], 'k' in [0,n-1]. 
          '(i,j)' represent two coordinates of the plate, 'k' represents a circuit.
          circuit_i_j_k is True IIF the circuit 'k' is present in the cell '(i,j)' of the plate.
        - coord_i_j_k, where 'i' in [0,w-w_min], 'j' in [0,l_max-h_min], 'k' in [0,n-1].
          '(i,j)' represent two coordinates of the plate, 'k' represents a circuit.
          coord_i_j_k is True IIF the left-bottom corner of the circuit 'k' is put in the cell '(i,j)' of the plate.
        - length_k_l, where 'k' in [0,n-1] and 'l' in [0,l_max-l_min].
          'k' represents a circuit, 'l' represents a length of the plate.
           length_k_l is True IIF the circuit 'k' uses the length 'l' of the plate.
           "A circuit uses a length" means that the circuit reaches or is above that length.
           Actually, the actual length corresponding to the variable 'length_k_l' is not 'l', but l+l_min: 'l' is just an 
           index on the variables 'length_k_l'.
           For going from an index 'l' of 'length_k_l' to the actual length: l+l_min.
           For going from an actual length 'l' to an index of 'length_k_l': l-l_min.
                Example. l_min=3, l_max=9.
                For each circuit 'k', the variables 'length_k_l' are: 
                            - length_k_0 (corresponding to the actual length 3)
                            - length_k_1 (corresponding to the actual length 4)
                            - length_k_2 (corresponding to the actual length 5)
                            ...
                            - length_k_6 (corresponding to the actual length 9)

        """
        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

        s = Solver()  # Solver instance

        # List of lists of lists, containing the 'circuits' boolean variables: variables 'circuit_i_j_k'
        circuits = [[[Bool(f'circuit_{i}_{j}_{k}') for k in range(n)] for j in range(l_max-h_min+1)] for i in range(w-w_min+1)]
        # List of lists of lists, containing the 'coords' boolean variables: variables 'coord_i_j_k'
        coords = [[[Bool(f'coord_{i}_{j}_{k}') for k in range(n)] for j in range(l_max-h_min+1)] for i in range(w-w_min+1)]
        # List of lists of lists, containing the 'lengths' boolean variables: variables 'length_k_l'
        lengths = [[Bool(f'length_{k}_{l}') for l in range(l_max-l_min+1)] for k in range(n)]
        
        # Constraint: in each cell '(i,j)' of the plate at most one circuit is present.
        # This reflects both on `circuits` and on `coords`.
        # (MAYBE REDUNDANT?)
        for i in range(w-w_min+1):
            for j in range(l_max-h_min+1):
                s.add(at_most_one(circuits[i][j], name=f'at_most_one_circuit_{i}_{j}'))  
                s.add(at_most_one(coords[i][j], name=f'at_most_one_coord_{i}_{j}'))
                
        # Constraint: the left-bottom corner of each circuit 'k' must be present exactly one time across the plate
        for k in range(n):
            s.add(exactly_one([coords[i][j][k] for i in range(w-w_min+1) for j in range(l_max-h_min+1)], name=f'exactly_one_{k}'))

        # Constraint: for each circuit 'k' and for each cell '(i,j)' of the plate, if that cell contains the left-bottom corner 
        # of 'k', then all the cells covered by the circuit 'k' must contain only that circuit and no other circuits.      
        for k in range(n):
            for i in range(w-w_min+1):
                for j in range(l_max-h_min+1):
                    # Current iteration: circuit `k` and cell `(i,j)` of the plate.
                    # Now the constraint about putting the left-bottom corner of `k` in `(i,j)` is ensured.

                    # Case in which `k` can't be put in `(i,j)`, because it goes out of the bounds of the plate.
                    # In such case, a constraint ensuring that `k` can't be put in `(i,j)` is added.
                    if i+dimsX[k]-1>=w or j+dimsY[k]-1>=l_max:
                        s.add(Not(coords[i][j][k]))  # The left-bottom corner of `k` can't be put in `(i,j)`
                        continue

                    # `k` can be put in `(i,j)`
                    
                    # List of tuples, representing the coordinates of the cells of the plate covered by the circuit
                    covered_positions = [(i+ii,j+jj) for ii in range(dimsX[k]) for jj in range(dimsY[k])
                                                    if i+ii<w-w_min+1 and j+jj<l_max-h_min+1]

                    # Formula ensuring that no other circuit is present in the `covered_positions`
                    no_overlapping_circuit_formula = And([Not(circuits[ii][jj][kk]) 
                                                        for (ii,jj) in covered_positions for kk in range(n) if kk!=k])
                    # Formula ensuring that all the `covered_positions` actually contain that circuit `k`
                    all_positions_covered_formula = And([circuits[ii][jj][k] for (ii,jj) in covered_positions])

                    # TODO: put negation of all circuits[ii][jj][k] related to wrong positions? 

                    # The added constraint is the following implication: if bottom-left corner of `k` is in `(i,j)`, then 
                    # `no_overlapping_circuit_formula` and `all_positions_covered_formula` are both True.
                    # Actually, it is not an implication, but an equivalence.
                    s.add(coords[i][j][k] == And(no_overlapping_circuit_formula,all_positions_covered_formula))
                    # (MAYBE THE EQUIVALENCE IS REDUNDANT? AN IMPLICATION WOULD BE ENOUGH?)

                    # Formula ensuring that all the lengths up to height of the circuit in the plate are used
                    used_lengths_formula = And([lengths[k][l] for l in range(j+dimsY[k]-l_min+1)])
                    # Formula ensuring that all the lengths from the height of the circuit in plate are not used
                    non_used_lengths_formula = And([Not(lengths[k][l]) for l in range(j+dimsY[k]-l_min+1, l_max-l_min+1)])
                    # The added constraint is the following implication: if bottom-left corner of `k` in `(i,j)`, then 
                    # `used_lengths_formula` and `non_used_lengths_formula` are both True.
                    # (`non_used_lengths_formula` IS MAYBE REDUNDANT?).
                    s.add(Implies(coords[i][j][k], And(used_lengths_formula, non_used_lengths_formula)))

        # Check if UNSAT 
        if s.check() != sat:
            raise UnsatError('UNSAT')
            
        return s, coords, lengths


    def __process_solver_instance(self, s, coords, lengths, w_min, h_min, l_min, l_max, current_best_l):
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
        w_min : int
            Minimum width of a circuit
        h_min : int
            Minimum height of a circuit
        l_min : int
            Lower bound of the length of the plate
        l_max : int
            Upper bound of the length of the plate
        current_best_l : int
            Current best length of the plate (found so far)

        Returns
        -------
        coords_sol : list of tuple of int
            Coordinates of the bottom-left corner of the circuits of the new extracted solution
        l : int
            Length of the plate of the new extracted solution
        """
        w, n = self.w, self.n

        if not current_best_l:
            current_best_l = l_max+1
        
        # Get the solution
        m = s.model()

        # List containing the coordX and coordY of the bottom-left vertex of each circuit in the new solution
        coords_sol = [(i, j) for k in range(n) for j in range(l_max-h_min+1) for i in range(w-w_min+1) if m.evaluate(coords[i][j][k])]
        # Boolean formula containing the new solution
        formula = And([ (coords[i][j][k] if m.evaluate(coords[i][j][k]) else Not(coords[i][j][k])) 
                    for i in range(w-w_min+1) for j in range(l_max-h_min+1) for k in range(n)])

        # Length of the plate in the new solution
        l = max([l for k in range(n) for l in range(l_max-l_min+1) if m.evaluate(lengths[k][l])])+l_min
        
        # Add into the solver the negation of the returned `formula`, which represents the current solution.
        # In this way, in the next iteration, the same solution is not feasible anymore
        s.add(Not(formula))  
        # (MAYBE REDUNDANT?)

        # Add into the solver a constraint ensuring that a solution which has a length bigger or equal than `l` is not feasible
        # anymore: in this way, the next found solution, if any, is for sure better than the previous one.
        # This is implemented by ensuring that all the variables 'lengths_k_ll' with 'll' from 'l' (included) to 
        # 'current_best_l' (exclued) are False.
        # In doing so, we have carefully compute the indeces corresponding to the actual lengths `l` and 'current_best_l'.
        #           'l' -> l-l_min
        #           'current_best_l' -> current_best_l-l_min
        s.add(And([Not(lengths[k][ll]) for k in range(n) for ll in range(l-l_min,current_best_l-l_min)]))
        
        return coords_sol, l


    def __optimize(self):
        """Solves the given VLSI instance, using the SAT encoding 3.

        It performs optimization: the best solution is found (if any).
        (If this class is used as a parallel process with a time limit, there is not gurantee of founding the optimal 
        solution, but only the best solution found so far).

        The implementation is based on the usage of the `__solve` method.
        The solver is created only one time, at the beginning. Then, a cycle is performed, in which at each iteration 
        new constraints are injected into the solver, namely: the constraints imposing that the already found solutions are not 
        feasible anymore (like in the previous encodings); the constraints imposing that the lengths of the plate bigger than 
        the current best length are not feasible anymore (this is done using the 'length_k_l' variables).

        Incremental solving.
        Linear search.

        Remark: imposing at each iteration that the solution must be different from the already found solution may be redundant, 
        since we are also imposing that the lengths of the plate bigger than the current best length are not feasible anymore.

        Raises
        ------
        UnsatError
            If the given instance is UNSAT

        Notes
        ------
        The solution is communicated to the user through the `results` dictionary, which is shared between the class and the 
        user. 
        Each time a better solution is found, it is injected into the `results` dictionary.
        
        """
        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

        areas = [dimsX[i]*dimsY[i] for i in range(n)]  # The areas of the circuits
        A_tot = sum(areas)  # The overall area of all the given circuits
        h_min = min(dimsY)  # The minimum height of a circuit
        h_max = max(dimsY)  # The maximum height of a circuit
        w_min = min(dimsX)  # The minimum width of a circuit
        w_max = max(dimsX)  # The maximum width of a circuit
        l_min = max([h_max, A_tot // w])  # The lower bound for the length
        min_rects_per_row = w // w_max  # Minimum number of circuits per row
        if min_rects_per_row==0:
            raise UnsatError('UNSAT')
        sorted_dimsY = sorted(dimsY, reverse=True)  
        if min_rects_per_row==1:
            l_max = sum(dimsY)
        else:
            l_max = sum([sorted_dimsY[i] for i in range(n) if i % min_rects_per_row == 0])  # The upper bound for the length

        # Search for a first solution 
        s, coords, lengths = self.__solve(w_min, h_min, l_min, l_max)
        self.results['best_coords'], self.results['best_l'] = self.__process_solver_instance(s, coords, lengths, w_min, 
                                                                                             h_min, l_min, l_max, 
                                                                                             current_best_l=None)

        # A first solution has been found
        
        while True:
            if s.check()!=sat:  # No more solutions: break the cycle
                break

            # A new solution has been found

            # Get the new valid solution and inject the new constraints into the solver
            self.results['best_coords'], self.results['best_l'] = self.__process_solver_instance(s, coords, lengths, w_min, 
                                                                                                 h_min, l_min, l_max, 
                                                                                                 self.results['best_l'])        
        
        # The computation is finished
        self.results['finish'] = True      


    def run(self):
        # Code executed by the process when it is runned
        try:
            self.__optimize()
        except UnsatError:
            self.results['unsat'] = True