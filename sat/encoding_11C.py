from z3 import *
from sat_utils import UnsatError, Vlsi_sat_abstract


class Vlsi_sat(Vlsi_sat_abstract):
    """Class for solving the VLSI problem in SAT, using the encoding 11C.

    It inherits from the class `Vlsi_sat_abstract`.

    Like the encoding 11C, also this encoding solves the rotation variant of the VLSI problem.

    The solving procedure is the same of the encoding 11C. SAT variables 'px_i_e', 'py_i_f, 'lr_i_j', 'ud_i_j', 'r_i' and 'ph_o'.
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
        """Solves the given VLSI instance, using the SAT encoding 11C.

        It is an auxiliary method. Its aim is to solve the VLSI instance without performing optimization: any solution is 
        good.

        Parameters
        ----------
        l_min : int
            Minimum length of the plate.
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
        r : list of z3.z3.BoolRef
            Boolean variables 'r_i'.
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
        - r_i, where 'i' represents a circuit. i in [0,n].
          r_i is True IFF the 'i'-th rectangle has been rotated, meaning that wi and hi have been swapped. 
        - ph_o, where 'o' represents a length.
          o in [0,l_max-l_min].
          'o' does not represent an actual length, but an index (on [l_min,l_max]). The corresponding actual length is l_o=o+l_min.
          ph_o is True IFF each circuit is below or at the same level of the length 'o' (i.e. l_o=o+l_min).    

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
        # List containing the 'r' boolean variables: variables 'r_i'
        r = [Bool(f'r_{i}') for i in range(n)]

        # List, containing the 'ph' boolean variables: variables 'ph_o'
        ph = [Bool(f'ph_{o}') for o in range(l_max-l_min+1)]
                
        # Ensure the constraint 1) and the constraints of the group A and B
        for i in range(n):
            for j in range(i+1,n):
                # Constraint 1)
                s.add( Or(lr[i][j],lr[j][i],ud[i][j],ud[j][i]) )

                # Group A
                # Constraint A1)
                if w-dimsX[i]-dimsX[j]<0:
                    s.add( Or(r[i], r[j], Not(lr[i][j])) )
                    s.add( Or(r[i], r[j], Not(lr[j][i])) )
                if w-dimsX[i]-dimsY[j]<0:
                    s.add( Or(r[i], Not(r[j]), Not(lr[i][j])) )
                    s.add( Or(r[i], Not(r[j]), Not(lr[j][i])) )
                if w-dimsY[i]-dimsX[j]<0:
                    s.add( Or(Not(r[i]), r[j], Not(lr[i][j])) )
                    s.add( Or(Not(r[i]), r[j], Not(lr[j][i])) )
                if w-dimsY[i]-dimsY[j]<0:
                    s.add( Or(Not(r[i]), Not(r[j]), Not(lr[i][j])) )
                    s.add( Or(Not(r[i]), Not(r[j]), Not(lr[j][i])) )

                # Constraints A2)
                for e in range(w-dimsX[i]+1):
                    if e < w-dimsX[i]-dimsX[j]+1:
                        s.add( Or(Not(lr[i][j]), r[i], r[j], px[i][e], Not(px[j][e+dimsX[i]])) )
                    if e < w-dimsX[i]-dimsY[j]+1:
                        s.add( Or(Not(lr[i][j]), r[i], Not(r[j]), px[i][e], Not(px[j][e+dimsX[i]])) )
                for e in range(w-dimsY[i]+1):
                    if e < w-dimsY[i]-dimsX[j]+1:
                        s.add( Or(Not(lr[i][j]), Not(r[i]), r[j], px[i][e], Not(px[j][e+dimsY[i]])) )
                    if e < w-dimsY[i]-dimsY[j]+1:
                        s.add( Or(Not(lr[i][j]), Not(r[i]), Not(r[j]), px[i][e], Not(px[j][e+dimsY[i]])) )
                # Constraints A3)
                for e in range(w-dimsX[j]+1):
                    if e < w-dimsX[j]-dimsX[i]+1:
                        s.add( Or(Not(lr[j][i]), r[j], r[i], px[j][e], Not(px[i][e+dimsX[j]])) )
                    if e < w-dimsX[j]-dimsY[i]+1:
                        s.add( Or(Not(lr[j][i]), r[j], Not(r[i]), px[j][e], Not(px[i][e+dimsX[j]])) )
                for e in range(w-dimsY[j]+1):
                    if e < w-dimsY[j]-dimsX[i]+1:
                        s.add( Or(Not(lr[j][i]), Not(r[j]), r[i], px[j][e], Not(px[i][e+dimsY[j]])) )
                    if e < w-dimsY[j]-dimsY[i]+1:
                        s.add( Or(Not(lr[j][i]), Not(r[j]), Not(r[i]), px[j][e], Not(px[i][e+dimsY[j]])) )

                # Constraint A4)
                for e in range(min([dimsX[i],w])):
                    s.add( Or(r[i], Not(lr[i][j]), Not(px[j][e])) )
                for e in range(min([dimsY[i],w])):
                    s.add( Or(Not(r[i]), Not(lr[i][j]), Not(px[j][e])) )
                # Constraint A5)
                for e in range(min([dimsX[j],w])):
                    s.add( Or(r[j], Not(lr[j][i]), Not(px[i][e])) )
                for e in range(min([dimsY[j],w])):
                    s.add( Or(Not(r[j]), Not(lr[j][i]), Not(px[i][e])) )

                # Group B
                # Constraint B1)
                if l_max-dimsY[i]-dimsY[j]<0:
                    s.add( Or(r[i], r[j], Not(ud[i][j])) )
                    s.add( Or(r[i], r[j], Not(ud[j][i])) )
                if l_max-dimsY[i]-dimsX[j]<0:
                    s.add( Or(r[i], Not(r[j]), Not(ud[i][j])) )
                    s.add( Or(r[i], Not(r[j]), Not(ud[j][i])) )
                if l_max-dimsX[i]-dimsY[j]<0:
                    s.add( Or(Not(r[i]), r[j], Not(ud[i][j])) )
                    s.add( Or(Not(r[i]), r[j], Not(ud[j][i])) )
                if l_max-dimsX[i]-dimsX[j]<0:
                    s.add( Or(Not(r[i]), Not(r[j]), Not(ud[i][j])) )
                    s.add( Or(Not(r[i]), Not(r[j]), Not(ud[j][i])) )

                # Constraints B2)
                for f in range(l_max-dimsY[i]+1):
                    if f < l_max-dimsY[i]-dimsY[j]+1:
                        s.add( Or(Not(ud[i][j]), r[i], r[j], py[i][f], Not(py[j][f+dimsY[i]])) )
                    if f < l_max-dimsY[i]-dimsX[j]+1:
                        s.add( Or(Not(ud[i][j]), r[i], Not(r[j]), py[i][f], Not(py[j][f+dimsY[i]])) )
                for f in range(l_max-dimsX[i]+1):
                    if f < l_max-dimsX[i]-dimsY[j]+1:
                        s.add( Or(Not(ud[i][j]), Not(r[i]), r[j], py[i][f], Not(py[j][f+dimsX[i]])) )
                    if f < l_max-dimsX[i]-dimsX[j]+1:
                        s.add( Or(Not(ud[i][j]), Not(r[i]), Not(r[j]), py[i][f], Not(py[j][f+dimsX[i]])) )
                # Constraints B3)
                for f in range(l_max-dimsY[j]+1):
                    if f < l_max-dimsY[j]-dimsY[i]+1:
                        s.add( Or(Not(ud[j][i]), r[j], r[i], py[j][f], Not(py[i][f+dimsY[j]])) )
                    if f < l_max-dimsY[j]-dimsX[i]+1:
                        s.add( Or(Not(ud[j][i]), r[j], Not(r[i]), py[j][f], Not(py[i][f+dimsY[j]])) )
                for f in range(l_max-dimsX[j]+1):
                    if f < l_max-dimsX[j]-dimsY[i]+1:
                        s.add( Or(Not(ud[j][i]), Not(r[j]), r[i], py[j][f], Not(py[i][f+dimsX[j]])) )
                    if f < l_max-dimsX[j]-dimsX[i]+1:
                        s.add( Or(Not(ud[j][i]), Not(r[j]), Not(r[i]), py[j][f], Not(py[i][f+dimsX[j]])) )

                # Constraint B4)
                for f in range(min([dimsY[i],l_max])):
                    s.add( Or(r[i], Not(ud[i][j]), Not(py[j][f])) )
                for f in range(min([dimsX[i],l_max])):
                    s.add( Or(Not(r[i]), Not(ud[i][j]), Not(py[j][f])) )
                # Constraint B5)
                for f in range(min([dimsY[j],l_max])):
                    s.add( Or(r[j], Not(ud[j][i]), Not(py[i][f])) )
                for f in range(min([dimsX[j],l_max])):
                    s.add( Or(Not(r[j]), Not(ud[j][i]), Not(py[i][f])) )

        # Ensure the constraints of the group C)
        for i in range(n):
            # Constraint C1)
            for e in range(w):
                if e>=w-dimsX[i]:
                    s.add(Or(r[i], px[i][e]))
                if e>=w-dimsY[i]:
                    s.add(Or(Not(r[i]), px[i][e]))
            # Constraint C2)
            for e in range(w-1):
                s.add( Or(Not(px[i][e]),px[i][e+1]) )           
            # Constraint C3)
            for f in range(l_max):
                if f>=l_max-dimsY[i]:
                    s.add(Or(r[i], py[i][f]))
                if f>=l_max-dimsX[i]:
                    s.add(Or(Not(r[i]), py[i][f]))
            # Constraint C4)
            for f in range(l_max-1):
                s.add( Or(Not(py[i][f]),py[i][f+1]) ) 

        # Ensure the constraint O1        
        for i in range(n):
            for o in range(l_max-l_min+1):
                s.add( Or(Not(ph[o]), r[i], py[i][o+l_min-dimsY[i]]) )
                s.add( Or(Not(ph[o]), Not(r[i]), py[i][o+l_min-dimsX[i]]) )
        # Ensure the constraint O2
        for o in range(l_max-l_min):
            s.add( Or(Not(ph[o]),ph[o+1]) )

        # WE DON'T RUN THE SOLVING
        
        return s, px, py, ph, r


    def __compute_coords_actualDims(self, s, px, py, r, l_max):
        """Computes the coords of the rectangles and the actual dimensions of the rectangles.
            - coords : coordinates of the lower-left verteces of the circuits.
              In the notation used above, coords correspond to the variables {xi,yi}_i.
            - actual dims : actual dimensions of the circuits, after their possible rotation.
              If a circuit has not been rotated, then its actual_dimsX is equal to its dimsX (i.e. w_i), and also its 
              actual_dimsY is equal to its dimsY (i.e. h_i).
              Instead, if a circuit has been rotated, then its actual_dimsX is equal to its dimsY, and its actual_dimsY is 
              equal to its dimsX.

        Parameters
        ----------
        s : z3.Solver
            The solver instance
        px : list of list of z3.z3.BoolRef
            Boolean variables 'px_i_e'.
        py : list of list of z3.z3.BoolRef
            Boolean variables 'py_i_f'.
        r : list of z3.z3.BoolRef
            Boolean variables 'r_i'.
        l_max : int
            Maximum length of the plate.

        Returns
        -------
        coords : list of tuple of int
            Coordinates of the left-bottom corner of the circuits.
        actual_dimsX : list of int
            Actual horizontal dimensions of the circuits, after their possible rotation.
        actual_dimsY : list of int
            Actual vertical dimensions of the circuits, after thei possible rotation.

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

        # If a circuit has not been rotated, then its actual_dimsX is equal to its dimsX, otherwise is equal to its dimsY.
        # The same for actual_dimsY.
        actual_dimsX = [self.dimsY[i] if m.evaluate(r[i]) else self.dimsX[i] for i in range(n)]
        actual_dimsY = [self.dimsX[i] if m.evaluate(r[i]) else self.dimsY[i] for i in range(n)]

        return coords, actual_dimsX, actual_dimsY


    def __optimize(self):
        """Solves the given VLSI instance, using the SAT encoding 11C.

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
        l_min =  A_tot // w  # The lower bound for the length
        max_dim = max(dimsX + dimsY)
        min_rects_per_row = w // max_dim 
        if min_rects_per_row<2:
            l_max = sum([max([dimsX[i],dimsY[i]]) for i in range(n)])
        else:
            sorted_dims = sorted([max([dimsX[i],dimsY[i]]) for i in range(n)], reverse=True)
            l_max = sum([sorted_dims[i] for i in range(n) if i % min_rects_per_row == 0])  # The upper bound for the length

        # Boolean flag reprenting if a first solution has already been found
        first_solution = False

        # Initializing the solver with all the constraints
        s, px, py, ph, r = self.__solve(l_min, l_max)

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
                coords, actual_dimsX, actual_dimsY = self.__compute_coords_actualDims(s, px, py, r, l_max)

                # Save the new best solution
                first_solution = True
                self.results['best_coords'] = coords
                self.results['best_l'] = l
                self.results['actual_dimsX'] = actual_dimsX
                self.results['actual_dimsY'] = actual_dimsY

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