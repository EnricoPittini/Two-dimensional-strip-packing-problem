from z3 import *
from sat_utils import at_least_one, at_most_one, exactly_one, UnsatError, Vlsi_sat_abstract
# from math import ceil


def eq(Xs, Ys):
    n = len(Xs)
    return And([Xs[i]==Ys[i] for i in range(n)])

def lex_lesseq(Xs, Ys):
    n = len(Xs)
    formulas = []
    for i in range(n):
        if i==0:
            formula = Or(Xs[i], Not(Ys[i]))
        else:
            formula = Implies(And([Xs[j]==Ys[j] for j in range(i)]), Or(Xs[i], Not(Ys[i])))
        formulas.append(formula)
    return And(formulas)

def lex_lesseq_compound(Xs, Ys):
    n = len(Xs)
    formulas = []
    for i in range(n):
        if i==0:
            formula = lex_lesseq(Xs[i], Ys[i])
        else:
            formula = Implies(And([eq(Xs[j],Ys[j]) for j in range(i)]), lex_lesseq(Xs[i], Ys[i]))
        formulas.append(formula)
    return And(formulas)



class Vlsi_sat(Vlsi_sat_abstract):
    """Class for solving the VLSI problem in SAT, using the encoding 4A.

    It inherits from the class `Vlsi_sat_abstract`.

    Same solving and optimization of the encoding 3.
    The only difference is the all the non-necessary constraints are removed.
    (The non-necessary constraints are both in `__solve` and in `__process_solver_instance`).

    """

    def __init__(self, w, n, dims, results):
        super().__init__(w, n, dims, results)


    def __solve(self, w_min, h_min, l_min, l_max):
        """Solves the given VLSI instance, using the SAT encoding 4A.

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
        - circuit_i_j_k, where 'i' in [0,w-w_min+1], 'j' in [0,l_max-h_min+1], 'k' in [0,n]. 
          '(i,j)' represent two coordinates of the plate, 'k' represents a circuit.
          circuit_i_j_k is True IIF the circuit 'k' is present in the cell '(i,j)' of the plate.
        - coord_i_j_k, where 'i' in [0,w-w_min+1], 'j' in [0,l_max-h_min+1], 'k' in [0,n].
          '(i,j)' represent two coordinates of the plate, 'k' represents a circuit.
          coord_i_j_k is True IIF the left-bottom corner of the circuit 'k' is put in the cell '(i,j)' of the plate.
        - length_k_l, where 'k' in [0,n] and 'l' in [0,l_max-l_min+1].
          'k' represents a circuit, 'l' represents a length of the plate.
           length_k_l is True IIF the circuit 'k' uses the length 'l' of the plate.
           For going from an index 'l' of 'length_k_l' to the actual length: l+l_min-1.
           For going from an actual length 'l' to an index of 'length_k_l': l-l_min+1.

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
        """ NON-NECESSARY
        for i in range(w-w_min+1):
            for j in range(l_max-h_min+1):
                s.add(at_most_one(circuits[i][j], name=f'at_most_one_circuit_{i}_{j}'))  # TODO : redundant?
                s.add(at_most_one(coords[i][j], name=f'at_most_one_coord_{i}_{j}'))"""
                
        # Constraint: the left-bottom corner of each circuit 'k' must be present exactly one time across the plate
        for k in range(n):
            s.add(exactly_one([coords[i][j][k] for i in range(w-w_min+1) for j in range(l_max-h_min+1)], name=f'exactly_one_{k}'))

        # print('CUCU')  # TODO: remove

        # Constraint: for each circuit 'k' and for each cell '(i,j)' of the plate, if that cell contains the left-bottom corner 
        # of 'k', then all the cells covered by the circuit 'k' must contain only that circuit and no other circuits.      
        for k in range(n):
            for i in range(w-w_min+1):
                for j in range(l_max-h_min+1):
                    # Current iteration: circuit `k` and cell `(i,j)` of the plate.
                    # Now the constraint about putting the left-bottom corner of `k` in `(i,j)` is ensured.

                    # Case in which `k` can't be put in `(i,j)`, because it goes out of the bounds of the plate.
                    # In such case, a constraint ensuring that `k` can't be put in `(i,j)` is esnured.
                    if i+dimsX[k]-1>=w or j+dimsY[k]-1>=l_max:
                        s.add(Not(coords[i][j][k]))  # The left-bottom corner of `k` can't be put in `(i,j)`
                        continue
                    
                    # List of tuples, representing the coordinates of the cells of the plate covered by the circuit
                    covered_positions = [(i+ii,j+jj) for ii in range(dimsX[k]) for jj in range(dimsY[k])
                                                    if i+ii<w-w_min+1 and j+jj<l_max-h_min+1]

                    # Formula ensuring that no other circuit is present in the `covered_positions`
                    no_overlapping_circuit_formula = And([Not(circuits[ii][jj][kk]) 
                                                        for (ii,jj) in covered_positions for kk in range(n) if kk!=k])
                    # Formula ensuring that all the `covered_positions` actually contain that circuit `k`
                    all_positions_covered_formula = And([circuits[ii][jj][k] for (ii,jj) in covered_positions])

                    # TODO: put negation of all circuits[ii][jj][k] related to wrong positions? 
                    # The added constraint is the following implication: if left-bottom corner of `k` in `(i,j)`, then 
                    # `no_overlapping_circuit_formula` and `all_positions_covered_formula`.
                    # Actually, it is not an implication, but an equivalence.
                    s.add(coords[i][j][k] == And(no_overlapping_circuit_formula,all_positions_covered_formula))

                    # Formula ensuring that all the lengths up to `j+dimsY[k]-1` are used by the circuit `k`
                    used_lengths_formula = And([lengths[k][l] for l in range(j+dimsY[k]-l_min+1)])
                    # Formula ensuring that all the lengths from `j+dimsY[k]` are not used by the circuit `k`
                    non_used_lengths_formula = And([Not(lengths[k][l]) for l in range(j+dimsY[k]-l_min+1, l_max-l_min+1)])
                    # The added constraint is the following implication: if left-bottom corner of `k` in `(i,j)`, then 
                    # `used_lengths_formula` and `non_used_lengths_formula`.
                    s.add(Implies(coords[i][j][k], And(used_lengths_formula, non_used_lengths_formula)))

        print('HERE')  # TODO: remove

        # SIMMETRY BREAKING
        correct_positions = [coords[i][j] for i in range(w-w_min+1) for j in range(l_max-h_min+1)]
        """s.add(lex_lesseq_compound(correct_positions, 
                                 [coords[w-w_min+1-i][j] for i in range(1, w-w_min+2) for j in range(l_max-h_min+1)]))"""
        s.add(lex_lesseq_compound(correct_positions, 
                                 [coords[i][l_max-h_min+1-j] for i in range(w-w_min+1) for j in range(1, l_max-h_min+2)]))
        """s.add(lex_lesseq_compound(correct_positions,
                                  [coords[w-w_min+1-i][l_max-h_min+1-j] for i in range(1, w-w_min+2) for j in range(1, l_max-h_min+2)]))"""

        print('HERE1')

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
            Coordinates of the left-bottom corner of the circuits of the new solution
        l : int
            Length of the plate of the new solution
        """
        w, n = self.w, self.n

        if not current_best_l:
            current_best_l = l_max+1
        
        # Get the solution
        m = s.model()

        # List containing the coordX and coordY of the lower-left vertex of each circuit in the new solution
        coords_sol = [(i, j) for k in range(n) for j in range(l_max-h_min+1) for i in range(w-w_min+1) if m.evaluate(coords[i][j][k])]
        # Boolean formula containing the new solution
        #formula = And([ (coords[i][j][k] if m.evaluate(coords[i][j][k]) else Not(coords[i][j][k])) 
        #            for i in range(w-w_min+1) for j in range(l_max-h_min+1) for k in range(n)])

        # Length of the plate in the new solution
        l = max([l for k in range(n) for l in range(l_max-l_min+1) if m.evaluate(lengths[k][l])])+l_min-1+1
        
        # Add into the solver the negation of the returned `formula`, which represents the current solution.
        # In this way, in the next iteration, the same solution is not feasible anymore
        """s.add(Not(formula))  NON-NECESSARY"""

        # Add into the solver a constraint ensuring that a solution which has a length bigger or equal than `l-1` is not feasible
        # anymore: in this way, the next found solution, if any, is for sure better than the previous one.
        # This is implemented by ensuring that all the variables 'lengths_k_ll' with 'll' from 'l-1' (included) to 
        # 'current_best_l-1' (exclued) are False.
        s.add(And([Not(lengths[k][ll]) for k in range(n) for ll in range(l-1-l_min+1,current_best_l-1-l_min+1)]))
        
        return coords_sol, l


    def __optimize(self):
        """Solves the given VLSI instance, using the SAT encoding 4A.

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
        h_min = min(dimsY)  # The minimum height of a circuit
        h_max = max(dimsY)  # The maximum height of a circuit
        w_min = min(dimsX)  # The minimum width of a circuit
        w_max = max(dimsX)  # The maximum width of a circuit
        l_min = max([h_max, A_tot // w])  # The lower bound for the length
        min_rects_per_row = w // w_max  # Minimum number of circuits per row
        # max_rects_per_col = ceil(n / max([1, min_rects_per_row]))  # Maximum number of circuits per column
        #l_max =  sum(sorted(dimsY)[n-max_rects_per_col:]) 
        if min_rects_per_row==0:
            raise UnsatError('UNSAT')
        sorted_dimsY = sorted(dimsY, reverse=True)  
        if min_rects_per_row==0:
            l_max = sum(dimsY)
        else:
            l_max = sum([sorted_dimsY[i] for i in range(n) if i % min_rects_per_row == 0])  # The upper bound for the length

        # Search for a first solution 
        s, coords, lengths = self.__solve(w_min, h_min, l_min, l_max)
        self.results['best_coords'], self.results['best_l'] = self.__process_solver_instance(s, coords, lengths, w_min, 
                                                                                             h_min, l_min, l_max, 
                                                                                             current_best_l=None)

        # A first solution has been found

        # print(self.results['best_coords'])
        # print(self.results['best_l'])
        
        # Loop iterating over all the possible solutions, searching for the best one
        while True:
            if s.check()!=sat:  # No more solutions: break the cycle
                break

            # A new solution has been found

            # Get the new valid solution and inject the new constraints into the solver
            self.results['best_coords'], self.results['best_l'] = self.__process_solver_instance(s, coords, lengths, w_min, 
                                                                                                 h_min, l_min, l_max, 
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