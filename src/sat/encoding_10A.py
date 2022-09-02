from z3 import *
from sat_utils import UnsatError, Vlsi_sat_abstract


class Vlsi_sat(Vlsi_sat_abstract):
    """Class for solving the VLSI problem in SAT, using the encoding 10A.

    It inherits from the class `Vlsi_sat_abstract`.

    The solving procedure is the same of the encoding 10. SAT variables 'px_i_e', 'py_i_f, 'lr_i_j' and 'ud_i_j'.
    In addition, there are also the SAT variables 'ph_o': they are introduced for improving the optimization procedure.
    See the `__solve` method.

    The optimization procedure has been improved, thanks to the variables 'ph_o'.
    In addition, the binary search is now used instead of the linear search. 
    Cycle. At each iteration we have a certain lower bound (i.e. lb) and a certain upper bound (i.e. ub) for the length of 
    the plate. We try to solve the problem, by running the solver from scratch, and by fixing the actual length of the plate 
    as smaller or equal than 'l', where 'l' is computed as ceil((lb+ub)/2). If SAT, we update ub<-l, if UNSAT we update 
    lb<-l+1. Then we repeat. 
    At the beginning, lb<-l_min (minimum length of the plate) and ub<-l_max (maximum length of the plate) 
    No incremental solving: at each iteration, the solver is created and run from scratch. 
    See the `__optimize` method.

    This improving of the optimization procedure, by means of the variables 'ph_o' and by means of the binary search, is 
    again taken from the paper *'A SAT-based Method for Solving the Two-dimensional Strip Packing Problem'*.


    --- VARIABLES ph_o ---
    These variables are again inspired by the order encoding, presented in the previous encoding class 10.

    ph_o, where 'o' represents a length.
    o in [0,l_max-l_min].
    'o' does not represent an actual length, but an index (on [l_min,l_max]). The corresponding actual length is l_o=o+l_min.
    So:
        from actual length 'l_o' to index 'o' ==> o=l_o-l_min;
        from index 'o' to actual length 'l_o' ==> l_o=o+l_min.
    ph_o is True IFF each circuit is below or at the same level of the length 'o'. 
    More precisely, ph_o is True IFF each circuit is below or at the same level of the length l_o=o+l_min.
    Formally:  ph_o is True IFF ∀i yi+hi<=l_o (where l_o=o+l_min)


    --- CONSTRAINTS ON ph_o ---
    For each circuit 'i' and for each 'o' in [0,l_max-l_min], we impose:
                ph_o -> py_i_{o+l_min-dimsY[i]}
    which is equivalent to:
                ¬ph_o \/ py_i_{o+l_min-dimsY[i]}
    Basically, this means that if ph_o is True then the circuit 'i' is below or at most the same level of the length l_o=o+l_min.
    Formally, yi+hi<=l_o, where l_o=o+l_min.
    On the whole, we have:
                ∀i∈[0,n-1] ∀o∈[0,l_mix-l_min] ¬ph_o \/ py_i_{o+l_min-dimsY[i]}

    Then, we put the usual constraint for the order encoding.
    Namely, for each 'o', we have to put:
                (¬ph_o \/ ph_{o+1})    (which is equivalent to ∀e (¬ph_o -> ph_{o+1}))

    Finally, we have to ensure that the actual length of the plate is smaller or equal the given 'l'.
    We simply add the constraint that ph_{l-l_min} is True.  (o=l-l_min is the index corresponding to the actual length 'l').
        

    --- SUM UP ---
    The constraints are the following.
    O1) ∀i∈[0,n-1] ∀o∈[0,l_mix-l_min] ¬ph_o \/ py_i_{o+l_min-dimsY[i]}
    O2) ∀o∈[0,l_mix-l_min-1] (¬ph_o \/ ph_{o+1})
    O3) ph_{l-l_min}

    """
    def __solve(self, l, l_min, l_max):
        """Solves the given VLSI instance, using the SAT encoding 10A.

        It is an auxiliary method. Its aim is to solve the VLSI instance without performing optimization: any solution is 
        good.

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

        if l<l_min:
            raise UnsatError('UNSAT')

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
        
        # The constraint O3 is ensured right away
        s.add( ph[l-l_min] )

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
                    
        if s.check() != sat:
            raise UnsatError('UNSAT')
        
        return s, px, py


    def __compute_coords(self, s, px, py, l_max):
        """Computes the coords of the circuits, namely the coordinates of the lower-left verteces of the circuits.

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
        """Solves the given VLSI instance, using the SAT encoding 10A.

        It performs optimization: the best solution is found (if any).
        (If this class is used as a parallel process with a time limit, there is not gurantee of founding the optimal 
        solution, but only the best solution found so far).

        The implementation is based on the usage of the `__solve` method.
        It is based on the binary search approach.
        Cycle. At each iteration we have a certain lower bound (i.e. lb) and a certain upper bound (i.e. ub) for the length of 
        the plate. We try to solve the problem, by running the solver from scratch using the `__solve` method, and by 
        fixing the actual length of the plate as smaller or equal than 'l', where 'l' is computed as ceil((lb+ub)/2). If SAT,
        we update ub<-l, if UNSAT we update lb<-l+1. Then we repeat. 
        At the beginning, lb<-l_min (minimum length of the plate) and ub<-l_max (maximum length of the plate) 
        No incremental solving: at each iteration, the solver is created and run from scratch. 
        See the `__optimize` method.

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

        # Upper and lower bounds for the length of the plate
        ub = l_max 
        lb = l_min 

        while lb<ub:
            # Modification which is necessary in the last iteration (where lb and ub differ only by 1)
            if lb+1==ub:
                ub = lb  

            # Current length of the plate of interest (in the middle of [lb,ub])  
            l = math.ceil((ub+lb)/2)
            #print(lb,ub,l)

            try:    
                # Search for a solution, given the current length of interest 'l' and given l_min<-lb and l_max<-ub
                s, px, py = self.__solve(l, lb, ub)

                # SAT: a solution has been found

                # Compute coords of the current solution
                coords = self.__compute_coords(s, px, py, l_max)

                # Save the new best solution
                first_solution = True
                self.results['best_coords'] = coords
                self.results['best_l'] = l
                # print(l)

                # Update ub<-l
                ub = l

            except UnsatError:
                # UNSAT: no new best solution

                # Update lb<-l+1
                lb = l+1

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