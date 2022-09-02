import os
from smt_utils import Vlsi_smt_abstract
import subprocess

class Vlsi_smt(Vlsi_smt_abstract):
    """Class for solving the VLSI problem in SMT, using the encoding 2A.

    It inherits from the class `Vlsi_smt_abstract`.

    The solving procedure is similar to the previous encodings. SMT variables 'coordX[i]' and 'coordY[i]'.
    In addition, there are also the SMT variable 'l'.
    See the `__solve` method.

    The optimization procedure has been improved, thanks to the variable 'l': it allows to perform the incremental 
    solving.
    Indeed, the SMT encoding is generated only one time, at the beginning. And the solver is started only one time, at the
    beginning (the solver is run on the terminal in incremental mode). 
    Then, a cycle is performed, in which at each iteration a new constraint is injected into the solver, namely the 
    constraint imposing that the length of the plate must be strictly smaller than the current best length already found 
    (this is imposed using the 'l' variable).
    We stop when we find UNSAT.
    Incremental solving.
    It is important to notice that we are performing a linear search, starting from the top (starting from the upper bound, 
    i.e. 'l_max').
    See the `__optimize` method.


    --- SUPPORTED SOLVERS ---
    Only solvers 'z3' and 'cvc5' are supported. No 'yices-smt2' ('yices-smt2' recquires that a specific logic is specified).

    """
    def __generate_encoding(self, l_max):
        """Generates the SMT encoding for the specific instance of the VLSI problem, according to the encoding 2A.

        The SMT encoding is generated as a single string, containing the SMT-LIB code, which will be passed to the solver.

        Parameters
        ----------
        l_max : int
            Maximum length of the plate.

        Returns
        -------
        encoding_string : str
            Single string containing the encoding. More specifically, it contains the SMT-LIB lines.

        Notes
        ------
        The following SMT variables are used.
        - coordX[i], where 'i' in [0,n-1].
          coordX[i] is the x coordinate of the bottom-left vertex of the 'i'-th circuit.
        - coordY[i], where 'i' in [0,n-1].
          coordY[i] is the y coordinate of the bottom-left vertex of the 'i'-th circuit.
        - l
          It represents the length of the plate.
          
        """
        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

        lines = []  # List of lines for the SMT-LIB encoding. It is a list of strings.

        # For getting the model
        lines.append('(set-option :produce-models true)')

        # VARIABLES
        # We are defining the function "coordX": we are declaring n variables "coordX[i]".
        lines.append('(declare-fun coordX (Int) Int)')
        # We are defining the function "coordY": we are declaring n variables "coordY[i]".
        lines.append('(declare-fun coordY (Int) Int)')
        # We are defining the variable "l".
        lines.append('(declare-fun l () Int)')

        # CONSTRAINTS

        # 1- Domains
        # We add a single string, stating that l<=l_max
        lines.append(f'(assert (<= l {l_max}))')

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

        # 3- Length of the plate
        # For each circuit 'i', we impose that coordY[i]+dimsY[i]<=l
        lines += [f'(assert (<= (+ (coordY {i}) {dimsY[i]}) l))' for i in range(n)]

        # CHECKING SATISFIABILITY AND GETTING THE MODEL
        lines.append('(check-sat)')
        # String "(get-value ((coordX 0) (coordX 1) ... (coordX N) (coordY 0) (coordY 1) ... (coordY N)))"
        lines.append(f'(get-value ({" ".join([f"(coordX {i}) (coordY {i}) " for i in range(n)])}))')

        # FINAL REFINEMENTS
        # Join all these strings, by means of the new line '\n'. Now we have a single string.
        encoding_string = '\n'.join(lines)
        # Add a final new line
        encoding_string += '\n'

        return encoding_string


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

    
    def __generate_new_constraint(self, current_best_l):
        """Generates the new constraint to add into the solver (incremental solving).

        More precisely, this new constraint involves the given `current_best_l`: we want to impose that the length of the 
        plate now must be strictly smaller than `current_best_l`.

        Parameters
        ----------
        current_best_l : int
            Current best length of the plate.

        Returns
        -------
        constraint_string : str
            Single string containing the encoding of the constraint (i.e. SMT-LIB lines). 

        """
        # Strings representing the SMT-LIB encoding of the new constraint to add
        lines = []

        # We impose that the length of the plate must be strictly smaller than the current best length: l<current_best_l
        lines.append(f'(assert (< l {current_best_l}))')

        # Check satisfiability and get the model
        lines.append('(check-sat)')
        lines.append(f'(get-value ({" ".join([f"(coordX {i}) (coordY {i}) " for i in range(self.n)])}))')

        # Join all these strings, by means of the new line '\n'. Now we have a single string.
        constraint_string = '\n'.join(lines)
        # Add a final new line.
        constraint_string += '\n'

        return constraint_string


    def __optimize(self):
        """Solves the given VLSI instance, using the SAT encoding 2A.

        It performs optimization: the best solution is found (if any).
        (If this class is used as a parallel process with a time limit, there is not gurantee of founding the optimal 
        solution, but only the best solution found so far).

        The optimization procedure has been improved, thanks to the variable 'l': it allows to perform the incremental 
        solving.
        Indeed, the SMT encoding is generated only one time, at the beginning. And the solver is started only one time, at the
        beginning. 
        Then, a cycle is performed, in which at each iteration a new constraint is injected into the solver, namely the 
        constraint imposing that the length of the plate must be strictly smaller than the current best length already found 
        (this is imposed using the 'l' variable).
        We stop when we find UNSAT.

        Incremental solving.

        It is important to notice that we are performing a linear search, starting from the top (starting from the upper bound, 
        i.e. 'l_max').

        Notes
        ------
        - The solver is run on the terminal in **incremental mode**. This means that the solver process remains alive, and 
          always waits for the user new constraints. 
        - The solution is communicated to the user through the `results` dictionary, which is shared between the class and the 
          user. 
          Each time a better solution is found, it is injected to the `results` dictionary.

        """
        solver_name = self.solver_name
        solver_path = os.path.join(os.getcwd(),'src', 'smt', 'solvers', solver_name)

        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

        # Boolean flag reprenting if a first solution has already been found
        first_solution = False

        # Computing the upper bound of the length of the plate (i.e. `l_max`)
        w_max = max(dimsX)  # The maximum width of a circuit
        min_rects_per_row = w // w_max  # Minimum number of circuits per row
        if min_rects_per_row==0:  # UNSAT
            self.results['finish'] = True
            self.results['unsat'] = True  
            return
        sorted_dimsY = sorted(dimsY, reverse=True)  
        if min_rects_per_row==1:
            l_max = sum(dimsY)
        else:
            l_max = sum([sorted_dimsY[i] for i in range(n) if i % min_rects_per_row == 0])  # The upper bound for the length

        # Command to execute on the terminal, for starting the solver process in incremental mode
        if solver_name=='z3':
            command = f'{solver_path} -in -T:{self.time_limit}'
        elif solver_name=='cvc5':
            command = f'{solver_path} --incremental --tlimit={self.time_limit*1000}'
        
        # Start the solver process on the terminal.
        # We use pipes for the stdin and the stdout of the solver process, for communicating with it.
        process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE)

        # Generate the string representing the SMT encoding
        encoding_string = self.__generate_encoding(l_max=l_max)

        # Pass to the solver process the SMT encoding
        process.stdin.write(encoding_string.encode('utf-8'))
        process.stdin.flush()

        # Get the solver process response
        output = process.stdout.read1().decode('utf-8')  # String sat/unsat
        output += process.stdout.read1().decode('utf-8') # String containing the model (if any)

        # Chech if UNSAT
        if 'unsat' in output:
            self.results['finish'] = True
            self.results['unsat'] = True 
            return 
        
        # SAT : a first solution has been found

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
        self.results['best_coords'] = coords
        self.results['best_l'] = l


        while True:        
            # Generate the new constraint to pass to the solver            
            constraint = self.__generate_new_constraint(l)

            # Pass the new constraint into the solver
            process.stdin.write(constraint.encode('utf-8'))
            process.stdin.flush()

            # Get the solver response
            output = process.stdout.read1().decode('utf-8')  # String sat/unsat
            output += process.stdout.read1().decode('utf-8') # String containing the model (if any)

            # Check if UNSAT
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