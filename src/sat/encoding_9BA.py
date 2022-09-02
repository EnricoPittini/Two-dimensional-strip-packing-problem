from z3 import *
from sat_utils import at_least_one, exactly_one, UnsatError, Vlsi_sat_abstract


class Vlsi_sat(Vlsi_sat_abstract):
    """Class for solving the VLSI problem in SAT, using the encoding 9B.

    It inherits from the class `Vlsi_sat_abstract`.

    Same solving and optimization of the encoding 9B. 
    Only difference: usage of the BITWISE encoding for the exactly_one constraint.

    """
    def __solve(self, w_min, h_min, l_min, l_max):
        """Solves the given VLSI instance, using the SAT encoding 9B.

        It is an auxiliary method. Its aim is to solve the VLSI instance without performing optimization: any solution is 
        good.

        Actually, it prepares only the solver by injecting all the necessary constraint, but it does not actually solve it.
        It simply configurates the solver.
        (It does not call the 's.check()' method).

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
                
        # Constraint: the left-bottom corner of each circuit 'k' must be present exactly one time across the plate
        """BITWISE ENCODING"""
        for k in range(n):
            s.add(exactly_one([coords[i][j][k] for i in range(w-w_min+1) for j in range(l_max-h_min+1)], name=f'exactly_one_{k}',
                  encoding='bitwise'))

        # print('CUCU')  # TODO: remove

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

                    # Formula ensuring that all the lengths up to `j+dimsY[k]-1` are used by the circuit `k`
                    used_lengths_formula = And([lengths[k][l] for l in range(j+dimsY[k]-l_min+1)])
                    # Formula ensuring that all the lengths from `j+dimsY[k]` are not used by the circuit `k`
                    non_used_lengths_formula = And([Not(lengths[k][l]) for l in range(j+dimsY[k]-l_min+1, l_max-l_min+1)])
                    # The added constraint is the following implication: if bottom-left corner of `k` in `(i,j)`, then 
                    # `used_lengths_formula` and `non_used_lengths_formula` are both True.
                    s.add(Implies(coords[i][j][k], And(used_lengths_formula, non_used_lengths_formula)))

        # WE DON'T RUN THE SOLVING
            
        return s, coords, lengths


    def __compute_coords_sol(self, s, coords, w_min, h_min, l_max):
        """Computes the coords of the circuits in the current solution, namely the coordinates of the bottom-left verteces of 
        the circuits in the current solution

        Parameters
        ----------
        s : z3.z3.Solver
            Solver instance
        coords : list of list of list of z3.z3.BoolRef
            Boolean variables 'coord_i_j_k'.
        w_min : int
            Minimum width of a circuit
        h_min : int
            Minimum height of a circuit
        l_max : int
            Upper bound of the length of the plate

        Returns
        -------
        coords_sol : list of tuple of int
            Coordinates of the bottom-left corner of the circuits of the new solution
        """
        w, n = self.w, self.n
        
        # Get the solution
        m = s.model()

        # List containing the coordX and coordY of the bottom-left vertex of each circuit in the new solution
        coords_sol = [(i, j) for k in range(n) for j in range(l_max-h_min+1) for i in range(w-w_min+1) if m.evaluate(coords[i][j][k])]

        return coords_sol



    def __optimize(self):
        """Solves the given VLSI instance, using the SAT encoding 9B.

        It performs optimization: the best solution is found (if any).
        (If this class is used as a parallel process with a time limit, there is not gurantee of founding the optimal 
        solution, but only the best solution found so far).

        The implementation uses the `__solve` method, which simply configurates the solver at the beginning.

        This optimization procedure consists in performing LINEAR SEARCH with incremental solving, but starting from the 
        bottom (i.e. l_min) instead of the top (i.e. l_max). 

        The solver is created only one time, at the beginning.
        Cycle. At each iteration we have a certain current 'l' that we want to try. We have already tested all the lengths below 
        'l', thus, if this 'l' is SAT, then this 'l' is the best possible 'l'.
        We inject into the solver a new constraint, ensuring that the actual length of the plate is smaller or equal than 'l'. 
        (Since we are sure that all the lengths below 'l' are not SAT, we are basically testing if 'l' is the best length for our
        problem). 
        Then, we solve that current solver instance.
        If SAT, then we simply take the best solution and we exit. If UNSAT, we update l<-l+1, we remove the last constraint 
        injected into the solver (i.e. the one ensuring that the actual length of the plate is smaller or equal than 'l') and we 
        add the new constraint ensuring that the actual length of the plate is strictly bigger than 'l'.
        Then we repeat. 
        At the beginning, l<-l_min.

        INCREMENTAL SOLVING: the solver is created only at the beginning, then we dinamically inject/remove constraints from that
        solver. For obtaining this behaviour, we use the assertions stack (we push/pop levels into that stack).

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

        # Boolean flag reprenting if a first solution has already been found
        first_solution = False

        # Initializing the solver with all the constraints
        s, coords, lengths = self.__solve(w_min, h_min, l_min, l_max)

        # Initial length of interest 'l'. We start from the bottom.
        l = l_min 
        
        # Loop iterating over all the possible solutions, searching for the best one, starting from the bottom
        while not first_solution and l<l_max:
            # We add the additional constraint ensuring that the actual length of the plate must be smaller or equal than 'l'.
            # More precisely, this constraints is about putting to False all variables 'length_k_ll' with 'll' from 'l'+1 to
            # the max length 'l_max'.
            # Be careful in transforming 'l' and 'l_max' from actual lengths to indeces before ensuring the constraint: l_index 
            # is l-l_min and the index of l_max is l_max-l_min.
            # We push this constraint into a new level of the assertions stack of the solver: in this way, we can retract 
            # this constraint, if necessary (if UNSAT).  
            s.push()
            l_index = l-l_min
            s.add(And([Not(lengths[k][ll]) for k in range(n) for ll in range(l_index+1,l_max-l_min+1)]))

            # Try to solve
 
            if s.check()==sat:  # SAT: we have found a solution
                # Compute the coords of the current solution
                coords_sol = self.__compute_coords_sol(s, coords, w_min, h_min, l_max)

                # Save the new best solution
                first_solution = True
                self.results['best_coords'] = coords_sol
                self.results['best_l'] = l

            else:   # UNSAT: no new best solution
                # We remove the last added constraint, namely the one ensuring that the actual length of the plate must be 
                # smaller or equal than 'l'. We retract that constraint.
                s.pop()

                # We add the new constraints ensuring that the actual length of the plate must be strictly bigger than 'l'.
                # More precisely, these constraints are that at least one variable among the n variables length_k_l is True and
                # at least one variable among the n variables length_k_{l+1} is True. 
                # Be careful in transforming 'l' from actual length to index before ensuring the constraint: l_index 
                # is l-l_min.
                # We add these constraints into the solver (we don't need to create a new level of the stack, because we don't 
                # need to retract this constraint).
                l_index = l-l_min
                s.add(at_least_one([lengths[k][l_index] for k in range(n)]))
                s.add(at_least_one([lengths[k][l_index+1] for k in range(n)]))

                l = l+1

        # The computation is finished
        self.results['finish'] = True       

        if not first_solution: # No solution has been found: UNSAT
            raise UnsatError('UNSAT')     


    def run(self):
        # Code executed by the process when it is runned
        try:
            self.__optimize()
        except UnsatError:
            self.results['unsat'] = True