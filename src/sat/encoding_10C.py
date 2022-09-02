from z3 import *
from sat_utils import UnsatError, Vlsi_sat_abstract


class Vlsi_sat(Vlsi_sat_abstract):
    """Class for solving the VLSI problem in SAT, using the encoding 10C.

    It inherits from the class `Vlsi_sat_abstract`.

    The solving procedure is the same of the encoding 10B. SAT variables 'px_i_e', 'py_i_f, 'lr_i_j', 'ud_i_j' and 'ph_o'.
    See the `__solve` method.

    The optimization is instead different. 
    The LINEAR SEARCH is used, but searching from the bottom instead of the top. 
    Basically, the search of the best 'l' starts from l_min instead of l_max.
    Still incremental solving and linear search, but from the bottom.

    The solver is created only one time, at the beginning.
    Cycle. At each iteration we have a certain current 'l' that we want to try. We have already tested all the lengths below 
    'l', thus, if this 'l' is SAT, then this 'l' is the best possible 'l'.
    We inject into the solver new constraints, ensuring that the actual length of the plate is smaller or equal than 'l' (i.e.
    ph_{l-l_min}). 
    (Since we are sure that all the lengths below 'l' are not SAT, we are basically testing if 'l' is the best length for our
    problem). 
    Then, we solve that current solver instance.
    If SAT, then we simply take the best solution and we exit. If UNSAT, we update l<-l+1, we remove the last constraint 
    injected into the solver (i.e. ph_{l-l_min}) and we add the new constraint ensuring that the actual length of the plate 
    is strictly bigger than 'l' (i.e. ¬ph_{l-l_min}).
    Then we repeat. 
    At the beginning, l<-l_min.

    INCREMENTAL SOLVING: the solver is created only at the beginning, then we dinamically inject/remove constraints from that
    solver. For obtaining this behaviour, we use the assertions stack (we push/pop levels into that stack).

    See the `__optimize` method.    

    """
    def __solve(self, l_min, l_max):
        """Solves the given VLSI instance, using the SAT encoding 10C.

        It is an auxiliary method. Its aim is to solve the VLSI instance without performing optimization: any solution is 
        good.

        Actually, it prepares only the solver by injecting all the necessary constraint, but it does not actually solve it.
        It simply configurates the solver.
        (It does not call the 's.check()' method).

        Parameters
        ----------
        l : int
            Length of the plate of interest.
        l_min : int
            Minimum length of the plate
        l_max : int
            Maximum length of the plate.

        Returns
        -------
        s : z3.Solver
            The solver instance
        px : list of list of z3.z3.BoolRef
            Boolean variables 'px_i_e'.
            See `Notes`.
        py : list of list of z3.z3.BoolRef
            Boolean variables 'py_i_f'.
            See `Notes`.
        ph : list of list of z3.z3.BoolRef
            Boolean variables 'ph_o'.
            See `Notes`.

        Raises
        ------
        UnsatError
            If the given instance is UNSAT

        Notes
        ------
        The following SAT variables are used.
        - px_i_e, where 'i' in [0,n-1] and 'e' in [0,w-1].
          'i' represents a circuit, 'e' a width of the plate.
          px_i_e is True IIF the x coordinate of left-bottom corner of the circuit 'i' is lower or equal than 'e' (i.e. xi<=e).
        - py_i_f, where 'i' in [0,n-1] and 'f' in [0,l_max-1].
          'i' represents a circuit, 'h' a length of the plate.
          py_i_f is True IIF the y coordinate of left-bottom corner of the circuit 'i' is lower or equal than 'f' (i.e. yi<=f).
        - lr_i_j, where 'i' and 'j' are in [0,n-1].
          'i' and 'j' represent two circuits.
          lr_i_j is True IIF the circuit 'i' is placed at the left to 'j'.
        - ud_i_j, where 'i' and 'j' are in [0,n-1].
          'i' and 'j' represent two circuits.
          ud_i_j is True IIF the circuit 'i' is placed at the downward to 'j'.  
        - ph_o, where 'o' represents a length.
          o in [0,l_max-l_min].
          'o' does not represent an actual length, but an index (on [l_min,l_max]). The corresponding actual length is l_o=o+l_min.
          So:
              from actual length 'l_o' to index 'o' ==> o=l_o-l_min;
              from index 'o' to actual length 'l_o' ==> l_o=o+l_min.
          ph_o is True IFF each circuit is below or at the same level of the length 'o'. 
          More precisely, ph_o is True IFF each circuit is below or at the same level of the length l_o=o+l_min.
          Formally:  ph_o is True IFF ∀i yi+hi<=l_o (where l_o=o+l_min)

        """
        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

        s = Solver()  # Solver instance

        # List of lists, containing the 'px' boolean variables: variables 'px_i_e'
        px = [[Bool(f'px_{i}_{e}') for e in range(w)] for i in range(n)]
        # List of lists, containing the 'py' boolean variables: variables 'py_i_f'
        py = [[Bool(f'py_{i}_{f}') for f in range(l_max)] for i in range(n)]
        # List of lists, containing the 'lr' boolean variables: variables 'lr_i_j'
        lr = [[Bool(f'lr_{i}_{j}') for j in range(n)] for i in range(n)]
        # List of lists, containing the 'ud' boolean variables: variables 'ud_i_j'
        ud = [[Bool(f'ud_{i}_{j}') for j in range(n)] for i in range(n)]

        # List, containing the 'ph' boolean variables: variables 'ph_o'
        ph = [Bool(f'ph_{o}') for o in range(l_max-l_min+1)]

        # Ensure the constraints of the group C)
        for i in range(n):
            # Constraint C2)
            for e in range(w-dimsX[i]):
                s.add( Or(Not(px[i][e]),px[i][e+1]) )  
            # Constraint C1)
            for e in range(w-dimsX[i],w):
                s.add(px[i][e])   
            # Constraint C4)
            for f in range(l_max-dimsY[i]):
                s.add( Or(Not(py[i][f]),py[i][f+1]) )      
            # Constraint C3)
            for f in range(l_max-dimsY[i],l_max):
                s.add(py[i][f])            

        # Ensure the constraint 1) and the constraints of the group A and B
        for i in range(n):
            for j in range(i+1,n):
                # Constraint 1)
                s.add( Or(lr[i][j],lr[j][i],ud[i][j],ud[j][i]) )

                # Group A
                # Constraint A1)
                if w-dimsX[i]-dimsX[j] < 0:
                    s.add( Not(lr[i][j]) )
                    s.add( Not(lr[j][i]) )
                else:
                    # Constraint A4)
                    for e in range(dimsX[i]):
                        s.add( Or(Not(lr[i][j]),Not(px[j][e])) )
                    # Constraint A5)
                    for e in range(dimsX[j]):
                        s.add( Or(Not(lr[j][i]),Not(px[i][e])) )
                    # Constraints A2) and A3)
                    for e in range(w-dimsX[i]-dimsX[j]+1):
                        s.add( Or(Not(lr[i][j]), px[i][e], Not(px[j][e+dimsX[i]])) )
                        s.add( Or(Not(lr[j][i]), px[j][e], Not(px[i][e+dimsX[j]])) )                    
                    
                # Group B
                # Constraint B1)
                if l_max-dimsY[i]-dimsY[j] < 0:
                    s.add( Not(ud[i][j]) )
                    s.add( Not(ud[j][i]) )
                else:
                    # Constraint B4)
                    for f in range(dimsY[i]):
                        s.add( Or(Not(ud[i][j]),Not(py[j][f])) )
                    # Constraint B5)
                    for f in range(dimsY[j]):
                        s.add( Or(Not(ud[j][i]),Not(py[i][f])) )
                    # Constraints B2) and B3)
                    for f in range(l_max-dimsY[i]-dimsY[j]+1):
                        s.add( Or(Not(ud[i][j]), py[i][f], Not(py[j][f+dimsY[i]])) )
                        s.add( Or(Not(ud[j][i]), py[j][f], Not(py[i][f+dimsY[j]])) )
                    
        # Ensure the constraint O1        
        for i in range(n):
            for o in range(l_max-l_min+1):
                s.add( Or(Not(ph[o]),py[i][o+l_min-dimsY[i]]) )
        # Ensure the constraint O2
        for o in range(l_max-l_min):
            s.add( Or(Not(ph[o]),ph[o+1]) )

        # WE DON'T RUN THE SOLVING
        
        return s, px, py, ph


    def __compute_coords(self, s, px, py, l_max):
        """Computes the coords of the rectangles, namely the coordinates of the bottom-left verteces of the circuits.

        In the notation used above, coords correspond to the variables {xi,yi}_i.

        Parameters
        ----------
        s : z3.Solver
            The solver instance
        px : list of list of z3.z3.BoolRef
            Boolean variables 'px_i_e'.
        py : list of list of z3.z3.BoolRef
            Boolean variables 'py_i_f'.
        l_max : int
            Maximum length of the plate.

        Returns
        -------
        coords : list of tuple of int
            Coordinates of the left-bottom corner of the circuits.

        """
        w, n = self.w, self.n
        m = s.model()

        # Suppose we want to find the value to assign to xi (i.e. x coordinate of the bottom-left corner of the i-th circuit).
        # For doing so, we iterate over all the variables px_i_e, from e=0: the first variable px_i_e corresponds to the 
        # value: the value of xi is that 'e'.
        # This is done for each xi.
        # The same reasoning is also applied to each yi (i.e. x coordinate of the bottom-left corner of the i-th circuit).
        coords = []
        for i in range(n):
            for e in range(w):
                if m.evaluate(px[i][e], model_completion=True):
                    coordX = e
                    break
            for f in range(l_max):
                if m.evaluate(py[i][f], model_completion=True):
                    coordY = f
                    break
            coords.append((coordX,coordY))

        return coords


    def __optimize(self):
        """Solves the given VLSI instance, using the SAT encoding 10C.

        It performs optimization: the best solution is found (if any).
        (If this class is used as a parallel process with a time limit, there is not gurantee of founding the optimal 
        solution, but only the best solution found so far).

        The implementation uses the `__solve` method, which simply configurates the solver at the beginning.

        This optimization procedure consists in performing incremental solving with linear search, starting from the bottom 
        (i.e. l_min).

        The solver is created only one time, at the beginning.
        Cycle. At each iteration we have a certain current 'l' that we want to try. We have already tested all the lengths below 
        'l', thus, if this 'l' is SAT, then this 'l' is the best possible 'l'.
        We inject into the solver new constraints, ensuring that the actual length of the plate is smaller or equal than 'l' (i.e.
        ph_{l-l_min}). 
        (Since we are sure that all the lengths below 'l' are not SAT, we are basically testing if 'l' is the best length for our
        problem). 
        Then, we solve that current solver instance.
        If SAT, then we simply take the best solution and we exit. If UNSAT, we update l<-l+1, we remove the last constraint 
        injected into the solver (i.e. ph_{l-l_min}) and we add the new constraint ensuring that the actual length of the plate 
        is strictly bigger than 'l' (i.e. ¬ph_{l-l_min}).
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
        Each time a better solution is found, it is injected to the `results` dictionary.

        """
        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

        areas = [dimsX[i]*dimsY[i] for i in range(n)]  # The areas of the circuits
        A_tot = sum(areas)  # The overall area of all the given circuits
        h_max = max(dimsY)  # The maximum height of a circuit
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
        s, px, py, ph = self.__solve(l_min, l_max)

        # Initial length of interest 'l'. We start from the bottom       
        l = l_min

        while not first_solution and l<l_max:
            #print(l)

            # We add the additional constraint ensuring that the actual length of the plate must be smaller or equal than 'l'.
            # Constraint: ph_{l-l_min}.
            # (We have to be careful in transforming 'l' from actual length to index before ensuring the constraint: l_index 
            # is l-l_min).
            # We push this constraint into a new level of the assertions stack of the solver: in this way, we can retract 
            # this constraint, if necessary (if UNSAT).       
            s.push()
            s.add( ph[l-l_min] )

            # Try to solve

            if s.check()==sat:  # SAT: we have found a solution
                # Compute the coords of the current solution
                coords = self.__compute_coords(s, px, py, l_max)

                # Save the new best solution
                first_solution = True
                self.results['best_coords'] = coords
                self.results['best_l'] = l

            else:  # UNSAT: no new best solution
                # We remove the last added constraint, namely the one ensuring that the actual length of the plate must be 
                # smaller or equal than 'l'. We retract that constraint.
                s.pop()

                # We add the new constraint ensuring that the actual length of the plate must be strictly bigger than 'l'.
                # Constraint: ¬ph_{l-l_min}.
                # (We have to be careful in transforming 'l' from actual length to index before ensuring the constraint: l_index 
                # is l-l_min).
                # We add these constraints into the solver (we don't need to create a new level of the stack, because we don't 
                # need to retract this constraint).
                s.add( Not(ph[l-l_min]) )

                # Update l
                l = l+1

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