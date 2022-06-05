from z3 import *
from sat_utils import at_least_one, at_most_one, exactly_one, UnsatError, Vlsi_sat_abstract
# from math import ceil


class Vlsi_sat(Vlsi_sat_abstract):
    """Class for solving the VLSI problem in SAT, using the encoding 6B.

    It inherits from the class `Vlsi_sat_abstract`.

    Both the solving and the optimization are very similar to the encoding 2.
    The only difference is about the bounds of the variables. 

    Better bounds for all the SAT variables: 'circuit_i_j_k', 'coord_i_j_k' and 'length_k_l'.
        1. 'circuit_i_j_k': i in [0,w-w_min+1], j in [0,l_max-h_min+1], k in [0,n]
        2. 'coord_i_j_k': i in [0,w-w_min+1], j in [0,l_max-h_min+1], k in [0,n]
        3. 'length_k_l': k in [0,n], l in [0,l_max-l_min+1]
            For going from an index 'l' of 'length_k_l' to the actual length: l+l_min-1.
            For going from an actual length 'l' to an index of 'length_k_l': l-l_min+1.

    """

    def __init__(self, w, n, dims, results):
        super().__init__(w, n, dims, results)


    def __solve(self, l_min, l_max):
        """Solves the given VLSI instance, using the SAT encoding 6B.

        It is an auxiliary method. Its aim is to solve the VLSI instance without performing optimization: any solution is 
        good.

        Parameters
        ----------
        l_min : int
            Lower bound of the length of the plate
        l_max : int
            Upper bound of the length of the plate

        Returns
        -------
        s: z3.z3.Solver
            The solver instance
        circuits : list of list of list of z3.z3.BoolRef
            Boolean variables 'circuits_i_j_k'.
            See `Notes`.
        lengths : list of list of z3.z3.BoolRef
            Boolean variables 'length_k_l'.
            See `Notes`.

        Notes
        ------
        The following boolean variables are used
        - circuit_i_j_k, where 'i' in [0,w-w_min+1], 'j' in [0,l_max-h_min+1], 'k' in [0,n]. 
          '(i,j)' represent two coordinates of the plate, 'k' represents a circuit.
          circuit_i_j_k is True IIF the circuit 'k' is present in the cell '(i,j)' of the plate.
        - length_l, where 'l' in [0, l_max-l_min+1].
           'l' represents a length of the plate.
           length_l is True IIF the length 'l'+l_min-1 is the maximum length of the plate.
           For going from an index 'l' of 'length_k_l' to the actual length: l+l_min-1.
           For going from an actual length 'l' to an index of 'length_k_l': l-l_min+1.

        """
        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

        s = Solver()  # Solver instance

        # List of lists of lists, containing the 'circuits' boolean variables: variables 'circuit_i_j_k'
        circuits = [[[Bool(f'circuit_{i}_{j}_{k}') for k in range(n)] for j in range(l_max)] for i in range(w)]
        # List of lists, containing the 'lengths' boolean variables: variables 'length_l'
        lengths = [Bool(f'length_{l}') for l in range(l_max-l_min+1)]
        
        # Constraint: in each cell '(i,j)' of the plate at most one circuit is present.
        for i in range(w):
            for j in range(l_max):
                s.add(at_most_one(circuits[i][j], name=f'at_most_one_circuit_{i}_{j}'))  

        print('CUCU')  # TODO: remove

        # Constraint: for each circuit 'k', we take all the possible configurations in which that circuit can be and we 
        # impose that exactly one of these configurations is True     
        for k in range(n):
            # Current iteration: circuit 'k'
            configurations_formulas = []  # List of formulas, in which each formula represents a possible configuration of 
                                          # that circuit
            for i in range(w):
                for j in range(l_max):
                    # Current iteration: circuit `k` and cell `(i,j)` of the plate.
                    # We want to create a formula (i.e. `configuration_formula`) representing the configuration consisting in
                    # putting the lower-left vertex of the circuit 'k' in the cell `(i,j)`

                    # Case in which `k` can't be put in `(i,j)`, because it goes out of the bounds of the plate.
                    # Basically, this configuration is not possible: we skip this configuration formula.
                    if i+dimsX[k]-1>=w or j+dimsY[k]-1>=l_max:
                        continue
                    
                    # List of tuples, representing the coordinates of the cells of the plate covered by the circuit in that
                    # configuration
                    covered_positions = [(i+ii,j+jj) for ii in range(dimsX[k]) for jj in range(dimsY[k])]
                    # List of tuples, representing the coordinates of the cells of the plate non-covered by the circuit in 
                    # that configuration
                    non_covered_positions = list(set([(ii,jj) for ii in range(w) for jj in range(l_max)]) 
                                                - set(covered_positions))
                    
                    # Formula ensuring that all the `covered_positions` actually contain that circuit `k`
                    all_positions_covered_formula = And([circuits[ii][jj][k] for (ii,jj) in covered_positions])  
                    # Formula ensuring that all the `non_covered_positions` don't contain that circuit `k`             
                    all_positions_not_covered_formula = And([Not(circuits[ii][jj][k]) for (ii,jj) in non_covered_positions])
                    
                    # TODO: put negation of all circuits[ii][jj][k] related to wrong positions? 
                    
                    # Formula representing the configuration consisting in putting the lower-left vertex of the circuit 'k' 
                    # in the cell `(i,j)`
                    configuration_formula = And(all_positions_covered_formula, all_positions_not_covered_formula)

                    configurations_formulas.append(configuration_formula)

            # We have collected the formulas of all the possible configurations for the circuit `k`: we impose that exactly
            # one of them is True
            s.add(exactly_one(configurations_formulas, name=f'exactly_one_{k}'))

        print('HERE')  # TODO: remove

        # Now we impose the constraints about the variables 'length_l'
        # First of all, exactly one variable must be True
        s.add(exactly_one(lengths))
        # Then, we have to impose a constraint for each possible length 'l', saying that the variable 'length_l' is True 
        # IFF there is at least one circuit reaching that length and no circuit goes above that length.
        for l in range(l_max-l_min+1):
            # Current iteration: length 'l'. It is the index of the variables 'length_l'
            # Let's compute the corresponding actual length of the plate
            l_actual = l+l_min-1
            # Formula saying that at least one circuit reaches that length of the plate
            at_least_one_circuit_reaches_that_length_formula = at_least_one([circuits[i][l_actual][k] 
                                                                        for i in range(w) for k in range(n)])
            # Formula saying that no circuits are above that length
            no_above_circuits_formula = And([Not(circuits[i][j][k]) 
                                             for i in range(w) for j in range(l_actual+1, l_max) for k in range(n)])
            # We add the formula: lengths[l] IFF at_least_one_circuit_reaches_that_length_formula AND no_above_circuits_formula
            s.add(lengths[l] == And(at_least_one_circuit_reaches_that_length_formula, no_above_circuits_formula))

        # Check if UNSAT 
        if s.check() != sat:
            raise UnsatError('UNSAT')
            
        return s, circuits, lengths


    def __process_solver_instance(self, s, circuits, lengths, l_min, l_max, current_best_l):
        """Processes the given solver instance.

        Two operations are performed:
            - the new solution is extracted from the given solver;
            - additional constraints are injected into the solver, in order to find the next best solution (incremental solving).

        Parameters
        ----------
        s : z3.z3.Solver
            Solver instance
        circuits : list of list of list of z3.z3.BoolRef
            Boolean variables 'circuits_i_j_k'.
        lengths : list of list of z3.z3.BoolRef
            Boolean variables 'length_k_l'.
        w_min : int
            Minimum width of a circuit
        h_min : int
            Minimum height of a circuit
        current_best_l : int
            Current best length of the plate (found so far)

        Returns
        -------
        coords_sol : list of tuple of int
            Coordinates of the left-bottom corner of the circuits of the new solution
        l : int
            Length of the plate of the new solution
        """
        w, n = self.w, self.n

        if not current_best_l:
            current_best_l = l_max+1
        
        # Get the solution
        m = s.model()
        
        # Coordinates of the left-bottom corner of the circuits of the new solution
        coords_sol = []    
        for k in range(n):
            coord = min([(i,j) for i in range(w) for j in range(l_max) if m.evaluate(circuits[i][j][k])])
            coords_sol.append(coord)

        # Length of the plate
        l = max([l for l in range(l_max-l_min+1) if m.evaluate(lengths[l])])+l_min-1+1

        # Add into the solver a constraint ensuring that a solution which has a length bigger or equal than `l-1` is not feasible
        # anymore: in this way, the next found solution, if any, is for sure better than the previous one.
        # This is implemented by ensuring that at least one of the variables 'length_l' with a smaller 'l' is True. 
        s.add(at_least_one([lengths[ll] for ll in range(l-1-l_min+1)]))
        
        return coords_sol, l


    def __optimize(self):
        """Solves the given VLSI instance, using the SAT encoding 6B.

        It performs optimization: the best solution is found (if any).
        (If this class is used as a parallel process with a time limit, there is not gurantee of founding the optimal 
        solution, but only the best solution found so far).

        The implementation is based on the usage of the `__solve` method.
        The solver is created only one time, at the beginning. Then, a cycle is performed, in which at each iteration 
        new constraints are injected into the solver, namely: the constraints imposing that the already found solutions are not 
        feasible anymore (like in the previous encodings); the constraints imposing that the lengths of the plate bigger than 
        the current best length are not feasible anymore (this is done using the 'length_k_l' variables).

        Incremental solving.

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
        # h_min = min(dimsY)  # The minimum height of a circuit
        h_max = max(dimsY)  # The maximum height of a circuit
        # w_min = min(dimsX)  # The minimum width of a circuit
        w_max = max(dimsX)  # The maximum width of a circuit
        l_min = max([h_max, A_tot // w])  # The lower bound for the length
        min_rects_per_row = w // w_max  # Minimum number of circuits per row
        # max_rects_per_col = ceil(n / max([1, min_rects_per_row]))  # Maximum number of circuits per column
        #l_max =  sum(sorted(dimsY)[n-max_rects_per_col:]) 
        if min_rects_per_row==0:
            raise UnsatError('UNSAT')
        sorted_dimsY = sorted(dimsY, reverse=True)  
        if min_rects_per_row==1:
            l_max = sum(dimsY)
        else:
            l_max = sum([sorted_dimsY[i] for i in range(n) if i % min_rects_per_row == 0])  # The upper bound for the length

        # Search for a first solution 
        s, circuits, lengths = self.__solve(l_min, l_max)
        self.results['best_coords'], self.results['best_l'] = self.__process_solver_instance(s, circuits, lengths, l_min, 
                                                                                             l_max, current_best_l=None)

        # A first solution has been found

        # print(self.results['best_coords'])
        # print(self.results['best_l'])
        
        # Loop iterating over all the possible solutions, searching for the best one
        while True:
            if s.check()!=sat:  # No more solutions: break the cycle
                break

            # A new solution has been found

            # Get the new valid solution and inject the new constraints into the solver
            self.results['best_coords'], self.results['best_l'] = self.__process_solver_instance(s, circuits, lengths, l_min,
                                                                                                 l_max, 
                                                                                                 self.results['best_l'])        
            # print(self.results['best_coords'])
            # print(self.results['best_l'])
        

        self.results['finish'] = True      


    def run(self):
        # Code executed by the process when it is runned
        try:
            self.__optimize()
        except UnsatError:
            self.results['unsat'] = True