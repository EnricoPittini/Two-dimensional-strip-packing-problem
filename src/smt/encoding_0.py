import os
from smt_utils import Vlsi_smt_abstract
import subprocess

class Vlsi_smt(Vlsi_smt_abstract):
    """Class for solving the VLSI problem in SMT, using the encoding 0.

    It inherits from the class `Vlsi_smt_abstract`.

    The solving procedure is based on the SMT variables 'coordX[i]' and 'coordY[i]'.
    See the `__generate_encoding` method.

    The optimization procedure is the following. Cycle, in which at each iteration the encoding is generated from scratch and
    the solver is created and run from scratch on that encoding. At each iteration, the current best length of the plate 
    (i.e. `l`) is given to the solver as upper bound for the length of the plate (i.e. `l_max`). (Actually, `l-1` is given as
    `l_max`).
    In this way, at each iteration is found a better solution with respect to the current one. We stop the cycle when we find
    UNSAT.
    The initial `l_max` is `sum(dimsY)`.
    No incremental solving: at each iteration, the solver is created and run from scratch. 
    See the `__optimize` method.


    --- SUPPORTED SOLVERS ---
    Only solvers 'z3' and 'cvc5' are supported. No 'yices-smt2' ('yices-smt2' recquires that a specific logic is specified).

    """
    def __generate_encoding(self, l_max):
        """Generates the SMT encoding for the specific instance of the VLSI problem, according to the encoding 0.

        The SMT encoding is generated into a SMT-LIB file, with name "encoding_0_{instance_name}.smt2".

        Parameters
        ----------
        l_max : int
            Maximum length of the plate.
            If None, `l_max` is computed as `sum(dimsY)`.

        Returns
        -------
        specificInstance_encoding_abspath : str
            Absolute path of the SMT encoding file for the specific instance.

        Notes
        ------
        The following SMT variables are used.
        - coordX[i], where 'i' in [0,n-1].
          coordX[i] is the x coordinate of the bottom-left vertex of the 'i'-th circuit.
        - coordY[i], where 'i' in [0,n-1].
          coordY[i] is the y coordinate of the bottom-left vertex of the 'i'-th circuit.

        """
        instance_name, w, n, dimsX, dimsY = self.instance_name, self.w, self.n, self.dimsX, self.dimsY

        # Upper bound of the length of the plate, if not explicitely given in input
        if not l_max:
            l_max = sum(dimsY)

        lines = []  # List of lines to write in the SMT-LIB file. It is a list of strings.

        # For getting the model
        lines.append('(set-option :produce-models true)')

        # VARIABLES
        # We are defining the function "coordX": we are declaring n variables "coordX[i]".
        lines.append('(declare-fun coordX (Int) Int)')
        # We are defining the function "coordY": we are declaring n variables "coordY[i]".
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
        # For each pair of circuits (i,j), where i<j, we impose the non-overlapping constraint: 
        #            coordX[i]+dimsX[i]<=coordX[j] \/ coordX[j]+dimsX[j]<=coordX[i] \/ coordY[i]+dimsY[i]<=coordY[j] \/ 
        #                                             coordY[j]+dimsY[j]<=coordY[i]
        lines += [f'(assert (or (<= (+ (coordX {i}) {dimsX[i]}) (coordX {j})) (<= (+ (coordX {j}) {dimsX[j]}) (coordX {i})) (<= (+ (coordY {i}) {dimsY[i]}) (coordY {j})) (<= (+ (coordY {j}) {dimsY[j]}) (coordY {i}))))' 
                for i in range(n) for j in range(n) if i<j]

        # CHECKING SATISFIABILITY AND GETTING THE MODEL
        lines.append('(check-sat)')
        # String "(get-value ((coordX 0) (coordX 1) ... (coordX N) (coordY 0) (coordY 1) ... (coordY N)))"
        lines.append(f'(get-value ({" ".join([f"(coordX {i}) (coordY {i}) " for i in range(n)])}))')

        # FINALLY, CREATING THE FILE AND WRITING THE LINES
        # Absolute path of the current directory
        curr_abs_path = os.path.dirname(os.path.abspath(__file__))
        # Absolute path of the SMT-LIB file containing the encoding of this specific VLSI instance
        specificInstance_encoding_abspath = os.path.join(curr_abs_path, f'encoding_0_{instance_name}.smt2')
        # Writing the lines into the file
        with open(specificInstance_encoding_abspath, 'w') as f:
            for line in lines:
                f.write(line + '\n')

        return specificInstance_encoding_abspath


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
        """Solves the given VLSI instance, using the SMT encoding 0.

        It performs optimization: the best solution is found (if any).
        (If this class is used as a parallel process with a time limit, there is not gurantee of founding the optimal 
        solution, but only the best solution found within the time limit).

        The implementation is based on the usage of the `__generate_encoding` method.

        The optimization procedure is the following. Cycle, in which at each iteration the encoding is generated from scratch
        and the solver is created and run from scratch on that encoding. At each iteration, the current best length of the 
        plate (i.e. `l`) is given to the solver as upper bound for the length of the plate (i.e. `l_max`). (Actually, `l-1` 
        is given as `l_max`).
        In this way, at each iteration is found a better solution with respect to the current one. 
        We stop the cycle when we find UNSAT.

        No incremental solving: at each iteration, the solver is created and run from scratch.

        Notes
        ------
        The solution is communicated to the user through the `results` dictionary, which is shared between the class and the 
        user. 
        Each time a better solution is found, it is injected to the `results` dictionary.

        """
        solver_name = self.solver_name

        # Boolean flag reprenting if a first solution has already been found
        first_solution = False

        solver_path = os.path.join(os.getcwd(),'src', 'smt', 'solvers', solver_name)
        #print(solver_path)

        while True:            
            # Compute the bound for the maximum length of the plate, i.e. l_max 
            if not first_solution:  # No solution for now
                l_max = None  
            else:  # At least one solution has already been found
                l_max = self.results['best_l']-1

            # Generate the SMT encoding, into a SMT-LIB file
            specific_encoding_path = self.__generate_encoding(l_max=l_max)

            # Run the solver on the generated SMT-LIB encoding
            command = f'{solver_path} "{specific_encoding_path}"'
            result = subprocess.run(command, capture_output=True)

            # Delete the SMT-LIB file containing the encoding
            os.remove(specific_encoding_path)

            # Get the output of the solver
            output = result.stdout.decode('UTF-8')

            # UNSAT: break the cycle
            if 'unsat' in output:
                break

            # SAT: a new solution has been found

            # Parse the output of the solver into the list of coords, i.e. `coords`
            if solver_name=='z3':
                coords = [int(s.split(')')[1]) for s in output.split('\n')[1:-1]]
            elif solver_name=='cvc5':
                coords = [int(s.split(')')[1]) for s in output.split('\n')[1:-1][0].split(' (')]
            # List of coords, for each circuit 'i'. For each circuit 'i', we have the list of two elements [coordX_i, coordY_i]
            coords = [[coords[2*i], coords[2*i+1]] for i in range((len(coords))//2)]
 
            # Length of the plate of the current solution
            l = self.__compute_l(coords)

            # TODO: remove
            #print(l)
            #print(coords)

            # Update the best solution found so far with the new solution
            first_solution = True
            self.results['best_coords'] = coords
            self.results['best_l'] = l

        # The computation is finished
        self.results['finish'] = True
                
        if not first_solution:  # No solution has been found: UNSAT
            self.results['unsat'] = True         


    def run(self):
        # Code executed by the process when it is run
        self.__optimize()