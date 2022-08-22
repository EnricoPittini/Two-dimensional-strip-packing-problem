import math
from time import sleep
from smt_utils import Vlsi_smt_abstract
import subprocess

class Vlsi_smt(Vlsi_smt_abstract):
    """Class for solving the VLSI problem in SMT, using the encoding 3D.

    It inherits from the class `Vlsi_smt_abstract`.

    It is exactly like the encoding 2B. Same SMT variables. Binary search optimization procedure.
    The only difference is that a specific SMT logic has been imposed.

    In particular, the "QF_LIA" logic has been imposed: "unquantified linear integer arithmetic. In essence, Boolean 
    combinations of inequations between linear polynomials over integer variables". 
    Basically, we have only Quantifier-Free formulas, with Linear Integer Arithmetic.

    This is a more specific logic with respect to the encoding 3A. Because now there aren't uninterpreted functions.

    Actually, for making the encoding compliant with the "QF_LIA" logic, we have to get rid of uninterpreted functions. 
    Basically, the we can have only uninterpreted constants.
    Therefore, we have to slightly change the encoding. 
    - We don't have anymore `n` variables coordX[0], ..., coordX[n-1], represented by the uninterpreted function `coordX[i]`.
    - But we have `n` variables coordX_0, ..., coordX_{n_1}.
    The same for coordY.
    The constraints remain exactly the same.
    See the `__generate_encoding` method.


    --- SUPPORTED SOLVERS ---
    All solvers 'z3', 'cvc5' and 'yices-smt2' are supported.

    """
    def __generate_encoding(self, l_max):
        """Generates the SMT encoding for the specific instance of the VLSI problem, according to the encoding 3D.

        The SMT encoding is generated as a single string, containing the SMT-LIB code, which will be passed to the solver.

        Remark: this returned string contains only the encoding, and it does not contain the SAT check and the "get model"
        instruction.

        Parameters
        ----------
        l_max : int
            Maximum length of the plate.

        Returns
        -------
        encoding_string : str
            Single string containing the encoding. More specifically, it contains the SMT-LIB lines.
            (Without the SAT check and the "get model" instruction).

        Notes
        ------
        The following SMT variables are used.
        - coordX_i, where 'i' in [0,n-1].
          coordX_i is the x coordinate of the bottom-left vertex of the 'i'-th circuit.
        - coordY_i, where 'i' in [0,n-1].
          coordY_i is the y coordinate of the bottom-left vertex of the 'i'-th circuit.
        - l
          It represents the length of the plate.
          
        """
        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

        lines = []  # List of lines for the SMT-LIB encoding. It is a list of strings.

        # For getting the model
        lines.append('(set-option :produce-models true)')
        # For setting the logic
        lines.append('(set-logic QF_LIA)')

        # VARIABLES
        # We are defining the function "coordX": we are declaring n variables "coordX_i".
        lines += [f'(declare-const coordX_{i} Int)' for i in range(n)]
        # We are defining the function "coordY": we are declaring n variables "coordY_i".
        lines += [f'(declare-const coordY_{i} Int)' for i in range(n)]
        # We are defining the variable "l".
        lines.append('(declare-const l Int)')

        # CONSTRAINTS

        # 1- Domains
        # We add a single string, stating that l<=l_max
        lines.append(f'(assert (<= l {l_max}))')

        # We create a list of strings, one for each variable "coordX[i]".
        # For each "coordX_i", we say that 0<="coordX_i"<=w-dimsX_i:
        lines += [f'(assert (and (>= coordX_{i} 0) (<= coordX_{i} (- {w} {dimsX[i]}))))' for i in range(n)]

        # We create a list of strings, one for each variable "coordY[i]".
        # For each "coordY_i", we say that 0<="coordY_i"<=l_max-dimsY_i:
        lines += [f'(assert (and (>= coordY_{i} 0) (<= coordY_{i} (- {l_max} {dimsY[i]}))))' for i in range(n)]

        # 2- Non-overlapping
        # For each pair of circuits (i,j), where i<j, we impose the non-overlapping constraint: 
        #            coordX_i+dimsX_i<=coordX_j \/ coordX_j+dimsX_j<=coordX_i \/ coordY_i+dimsY_i<=coordY_j \/ 
        #                                             coordY_j+dimsY_j<=coordY_i
        lines += [f'(assert (or (<= (+ coordX_{i} {dimsX[i]}) coordX_{j}) (<= (+ coordX_{j} {dimsX[j]}) coordX_{i}) (<= (+ coordY_{i} {dimsY[i]}) coordY_{j}) (<= (+ coordY_{j} {dimsY[j]}) coordY_{i})))' 
                for i in range(n) for j in range(n) if i<j]
        
        # 3- Length of the plate
        # For each circuit 'i', we impose that coordY_i+dimsY_i<=l
        lines += [f'(assert (<= (+ coordY_{i} {dimsY[i]}) l))' for i in range(n)]

        # FINAL REFINEMENTS
        # Join all these strings, by means of the new line '\n'. Now we have a single string.
        encoding_string = '\n'.join(lines)
        # Add a final new line
        encoding_string += '\n'

        return encoding_string

    
    def __generate_new_constraint(self, l_med):
        """Generates the new constraint to add into the solver (incremental solving).

        More precisely, this new constraint involves the given `l_med`, which is in the middle of the current interval [lb,ub].
        We want to impose that the length of the plate must be smaller or equal than `l_med`.

        Parameters
        ----------
        l_med : int
            Current length of interest of the plate. It's the middle of the current interval [lb,ub].

        Returns
        -------
        constraint_string : str
            Single string containing the encoding of the constraint (i.e. SMT-LIB lines). 

        """
        # Strings representing the SMT-LIB encoding of the new constraint to add
        lines = []
       
        # We push the new constraint into a new level of the assertions stack of the solver: in this way, we can retract 
        # this constraint, if necessary (if UNSAT).  
        lines.append('(push 1)')

        # We impose that the length of the plate must be smaller or equal than the current given length: l<=l_med
        lines.append(f'(assert (<= l {l_med}))')

        # Check satisfiability and get the model
        lines.append('(check-sat)')
        # String "(get-value (coordX_0 coordX_1 ... coordX_N coordY_0 coordY_1 ... coordY_N))"
        lines.append(f'(get-value ({" ".join([f"coordX_{i} coordY_{i} " for i in range(self.n)])}))')

        # Join all these strings, by means of the new line '\n'. Now we have a single string.
        constraint_string = '\n'.join(lines)
        # Add a final new line.
        constraint_string += '\n'

        return constraint_string


    def __optimize(self):
        """Solves the given VLSI instance, using the SAT encoding 3D.

        It performs optimization: the best solution is found (if any).
        (If this class is used as a parallel process with a time limit, there is not gurantee of founding the optimal 
        solution, but only the best solution found so far).

        The optimization procedure is the following.
        The SMT encoding is generated only one time, at the beginning. And the solver is started only one time, at the
        beginning (the solver is run on the terminal in incremental mode).
        Cycle. At each iteration we have a certain lower bound (i.e. lb) and a certain upper bound (i.e. ub) for the length of 
        the plate. We take as length of the plate of interest 'l_med' the middle between lb and ub. We inject into the solver a new 
        constraint, ensuring that the actual length of the plate is smaller or equal than 'l_med'.  
        Then, we solve that current solver instance.
        If SAT, then we simply update ub<-l-1. If UNSAT, we update lb<-l_med+1, we remove the last constraint injected into the
        solver (i.e. the one ensuring that the actual length of the plate is smaller or equal than 'l_med') and we add the new 
        constraint ensuring that the actual length of the plate is strictly bigger than 'l_med'.
        Then we repeat. 
        At the beginning, lb<-l_min (minimum length of the plate) and ub<-l_max (maximum length of the plate) 

        INCREMENTAL SOLVING: the solver is created only at the beginning, then we dinamically inject/remove constraints from that
        solver. For obtaining this behaviour, we use the assertions stack (we push/pop levels into that stack).

        Notes
        ------
        - The solver is run on the terminal in **incremental mode**. This means that the solver process remains alive, and 
          always waits for the user new constraints. 
        - The solution is communicated to the user through the `results` dictionary, which is shared between the class and the 
          user. 
          Each time a better solution is found, it is injected to the `results` dictionary.

        """
        solver_name = self.solver_name

        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

        # Computing the lowe and upper bound of the length of the plate (i.e. `l_min` and `l_max`)
        areas = [dimsX[i]*dimsY[i] for i in range(n)]  # The areas of the circuits
        A_tot = sum(areas)  # The overall area of all the given circuits
        h_max = max(dimsY)  # The maximum height of a circuit
        w_max = max(dimsX)  # The maximum width of a circuit
        l_min = max([h_max, A_tot // w])  # The lower bound for the length
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
            command = f'z3 -in -T:{self.time_limit}'
        elif solver_name=='cvc5':
            command = f'cvc5 --incremental --tlimit={self.time_limit*1000}'
        elif solver_name=='yices-smt2':
            command = f'yices-smt2 --incremental --timeout={self.time_limit}'
        
        # Start the solver process on the terminal.
        # We use pipes for the stdin and the stdout of the solver process, for communicating with it.
        process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE)

        # Generate the string representing the SMT encoding
        encoding = self.__generate_encoding(l_max=l_max)

        # Pass to the solver process the SMT encoding
        process.stdin.write(encoding.encode('utf-8'))
        process.stdin.flush()
    
        # Starting lower and upper bounds for the length of the plate: `lb` and `ub`
        lb = l_min-1
        ub = l_max

        while lb<ub:      
            # Current length of interest of the plate (in the middle of [lb,ub])    
            l_med = math.ceil((ub+lb)/2)

            # Generate the new constraint to pass to the solver
            constraint = self.__generate_new_constraint(l_med)

            # Pass the new constraint into the solver
            process.stdin.write(constraint.encode('utf-8'))
            process.stdin.flush()

            # Get the solver response
            output = process.stdout.read1().decode('utf-8') # String sat/unsat
            if solver_name=='yices-smt2':
                sleep(0.00000000000000000001)
            output += process.stdout.read1().decode('utf-8') # String containing the model (if any)
            #sleep(0.00000000000000000001)

            #print(output)

            if 'unsat' in output:  # UNSAT
                # Pop out the last imposed constraint (the one ensuring that the length of the plate must be smaller or equal
                # than `l_med`)
                process.stdin.write('(pop 1)'.encode('utf-8'))

                # Add a new constraint into the solver, ensuring that the length of the plate must be strictly greater than
                # `l_med`
                process.stdin.write(f'(assert (> l {l_med}))'.encode('utf-8'))

                # Update the lower bound
                lb = l_med+1

            elif 'sat' in output:  # SAT : a new best solution has been found
                # Parse the output of the solver into the list of coords, i.e. `coords`
                if solver_name=='z3' or solver_name=='yices-smt2':
                    coords = [int(s.split(')')[0].split(' ')[-1]) for s in output.split('\n')[1:-1]]
                elif solver_name=='cvc5':
                    coords = [int(s.split(')')[0].split(' ')[-1]) for s in output.split('\n')[1:-1][0].split(' (')]
                # List of coords, for each circuit 'i'. For each circuit 'i', we have the list of two elements [coordX_i, coordY_i]
                coords = [[coords[2*i], coords[2*i+1]] for i in range((len(coords))//2)]

                # TODO: remove
                #print(l_med)
                #print(coords)

                # Update the best solution found so far with the new solution
                self.results['best_coords'] = coords
                self.results['best_l'] = l_med

                # Update the upper bound
                ub = l_med-1


        # The computation is finished
        self.results['finish'] = True
                
        if lb>ub:  # No solution has been found: UNSAT
            self.results['unsat'] = True         


    def run(self):
        # Code executed by the process when it is run
        self.__optimize()