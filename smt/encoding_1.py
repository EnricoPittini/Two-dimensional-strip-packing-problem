import os
from smt_utils import Vlsi_smt_abstract
import subprocess

class Vlsi_smt(Vlsi_smt_abstract):
    def __generate_encoding(self, l_max):
        instance_name, w, n, dimsX, dimsY = self.instance_name, self.w, self.n, self.dimsX, self.dimsY

        lines = []  # List of lines to write in the SMT-LIB file. It is a list of strings.

        lines.append('(set-option :produce-models true)')

        # VARIABLES
        # We are defining the function "coordX". We are declaring n variables "coordX[i]".
        lines.append('(declare-fun coordX (Int) Int)')
        # We are defining the function "coordY". We are declaring n variables "coordY[i]".
        lines.append('(declare-fun coordY (Int) Int)')

        # CONSTRAINTS

        # 1- Domains
        # We create a list of strings, one for each variable "coordX[i]".
        # For each "coordX[i]", we say that 0<="coordX[i]"<=w-dimsX[i]:
        #                        "(assert (and (>= (coordX {i}) 0) (<= (coordX {i}) (- {w} {dimsX[i]}))))".
        lines += [f'(assert (and (>= (coordX {i}) 0) (<= (coordX {i}) (- {w} {dimsX[i]}))))' for i in range(n)]

        # We create a list of strings, one for each variable "coordY[i]".
        # For each "coordY[i]", we say that 0<="coordY[i]"<=l_max-dimsY[i]:
        #                        "(assert (and (>= (coordY {i}) 0) (<= (coordY {i}) (- {l_max} {dimsY[i]}))))".
        lines += [f'(assert (and (>= (coordY {i}) 0) (<= (coordY {i}) (- {l_max} {dimsY[i]}))))' for i in range(n)]

        # 2- Non-overlapping
        # For each pair of circuits i-j, we impose the non-overlapping constraint
        lines += [f'(assert (or (<= (+ (coordX {i}) {dimsX[i]}) (coordX {j})) (<= (+ (coordX {j}) {dimsX[j]}) (coordX {i})) (<= (+ (coordY {i}) {dimsY[i]}) (coordY {j})) (<= (+ (coordY {j}) {dimsY[j]}) (coordY {i}))))' 
                for i in range(n) for j in range(n) if i<j]

        # CHECKING SATISFIABILITY AND GETTING THE MODEL
        lines.append('(check-sat)')
        # String "(get-value ((coordX 0) (coordX 1) ... (coordX N) (coordY 0) (coordY 1) ... (coordY N)))"
        lines.append(f'(get-value ({" ".join([f"(coordX {i}) (coordY {i}) " for i in range(n)])}))')

        # FINALLY, CREATING THE FILE AND WRITING THE LINES
        curr_abs_path = os.path.dirname(os.path.abspath(__file__))
        # print(curr_abs_path)
        specific_instance_abspath = os.path.join(curr_abs_path, f'encoding_1_{instance_name}.smt2')
        with open(specific_instance_abspath, 'w') as f:
            for line in lines:
                f.write(line + '\n')

        return specific_instance_abspath


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
        solver_name = self.solver_name

        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

        # Boolean flag reprenting if a first solution has already been found
        first_solution = False

        w_max = max(dimsX)  # The maximum width of a circuit
        min_rects_per_row = w // w_max  # Minimum number of circuits per row
        if min_rects_per_row==0:
            self.results['finish'] = True
            self.results['unsat'] = True  
            return
        sorted_dimsY = sorted(dimsY, reverse=True)  
        if min_rects_per_row==1:
            l_max = sum(dimsY)
        else:
            l_max = sum([sorted_dimsY[i] for i in range(n) if i % min_rects_per_row == 0])  # The upper bound for the length

        while True:           
            # Search for a solution, given the additional constraints in `formulas` and given the current l_max
            specific_encoding_path = self.__generate_encoding(l_max=l_max)
            command = f'{solver_name} "{specific_encoding_path}"'

            result = subprocess.run(command, capture_output=True)

            os.remove(specific_encoding_path)

            output = result.stdout.decode('UTF-8')
            #print(output)

            if 'unsat' in output:
                break

            # SAT: a new solution has been found
            
            if solver_name=='z3':
                coords = [int(s.split(')')[1]) for s in output.split('\n')[1:-1]]
            elif solver_name=='cvc5':
                coords = [int(s.split(')')[1]) for s in output.split('\n')[1:-1][0].split(' (')]
            #print(coords)
            coords = [[coords[2*i], coords[2*i+1]] for i in range((len(coords))//2)]
 
            # Length of the plate of the current solution
            l = self.__compute_l(coords)

            # TODO: remove
            print(l)
            print(coords)

            # Update the best solution found so far with the new solution
            first_solution = True
            self.results['best_coords'] = coords
            self.results['best_l'] = l

            l_max = self.results['best_l']-1

        # The computation is finished
        self.results['finish'] = True
                
        if not first_solution:  # No solution has been found: UNSAT
            self.results['unsat'] = True         


    def run(self):
        # Code executed by the process when it is runned
        self.__optimize()