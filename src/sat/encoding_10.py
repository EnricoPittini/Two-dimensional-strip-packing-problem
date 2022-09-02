from z3 import *
from sat_utils import UnsatError, Vlsi_sat_abstract


class Vlsi_sat(Vlsi_sat_abstract):
    """Class for solving the VLSI problem in SAT, using the encoding 10.

    It inherits from the class `Vlsi_sat_abstract`.

    This is a completely different encoding from the previous ones.
    This encoding has been taken from the paper *'A SAT-based Method for Solving the Two-dimensional Strip Packing Problem'*.

    The main idea is the following.
    The basic CP model is considered. Namely, the one in which the non-overlapping of each couple of rectangles i-j is 
    ensured by means of a disjunction of four constraints: 
                        (xi + wi ≤ xj ) \/ (xj + wj ≤ xi) \/ (yi + hi ≤ yj ) \/ (yj + hj ≤ yi).
    (Scheduling-like constraints).
    Then, these constraints are encoded into SAT using the ORDER ENCODING.
    See the description below.

    A basic optimization procedure has been used.
    Cycle in which at each iteration the solver is created and run from scratch, with the current best length of the plate 
    (i.e. `l`) given to the solver as upper bound for the length of the plate (i.e. `l_max`). (Actually, `l-1` is given as 
    `l_max`). 
    In this way, at each iteration is found a better solution with respect to the current one.
    No incremental solving: at each iteration, the solver is created and run from scratch. 
    See the `__optimize` method.


    --- NOTATION ---
    The notation used in the following description follows the notation of the paper, and it may differ from the notation 
    used for the previous encodings.

    n : number of circuits.
    w : width of the plate.
    l_max : max length of the plate.
    wi : width of the i-th circuit.
    hi : height of the i-th circuit.
    xi : x coordinate of the left-bottom corner of the i-th circuit.
    yi : y coordinate of the left-bottom corner of the i-th circuit. 


    --- ORDER ENCODING ---
    Order encoding consists in two steps.
    First of all, the constraints are reduced to combinations of constraints of the form  xi ≤ c  (where xi is a variable and
    c a constant).
    Then, each constraint   xi ≤ c  is encoded as a SAT variable  px_i_c.     px_i_c  <->  xi ≤ c                   

    Example.
    Constraint  x1 + 1 ≤ x2 , where x1 and x2 are two variables in {0,1,2,3}.
        - Step 1.
          The given constraint is equivalent to the following ones:
                (x2>0) /\ (x2≤1 -> x1≤0) /\ (x2≤2 -> x1≤1) /\ x1≤2
          Which are equivalent to:
                ¬(x2≤0) /\ (¬(x2≤1) \/ x1≤0) /\ (¬(x2≤2) \/ x1≤1) /\ x1≤2
        - Step 2.
          Encoding using SAT variables.
                ¬px_2,0 /\ (px_1,0 \/ ¬px_2,1) /\ (px_1,1 \/ ¬px_2,2) /\ px_1,2

    Actually, these constraints are not enough. We have to specify other constraints about the variables px_ic.
    We have to encode the fact that, if px_ic is True, then all px_id with d>c are True.
            ∀c (px_ic -> px_i{c+1})
    Which is equivalent to:
            ∀c (¬px_ic \/ px_i{c+1})

    In the example, we have also the constraints:
        (px_10 -> px_11) /\ (px_11 -> px_12) /\ (px_20 -> px_21) /\ (px_21 -> px_22)
    Which are equivalent to:
        (¬px_10 \/ px_11) /\ (¬px_11 \/ px_12) /\ (¬px_20 \/ px_21) /\ (¬px_21 \/ px_22)

    Given a model for our problem, consisting in an assignement of truth values to the boolean variables px_ic, how can we 
    deduce the value assigned to each variable xi?
    For each variable xi, we take all the associated boolean variables px_ic, we scan them from the smallest c to the 
    biggest c, and we stop when we find the first True boolean variable px_id : d is the value associated to the variable 
    xi.
    (Why? Because we have that all px_ic with c<d are False, and all px_ic with c>=d are True).

    In the example, if in the model we have:
        px_10=False, px_11=True, px_12=True
    then the value assigned to x1 is 1.
    

    --- APPLICATION OF THE ORDER ENCODING IN OUR PROBLEM ---
    The following boolean variables are used.
        1) px_i_e, where 'i' represents a circuit and 'e' represents a value in [0,w].
           i in [0,n], e in [0,w].
           px_i_e is True IFF xi≤e. Which means that the x coordinate of the left-bottom corner of circuit 'i' has been placed
           less or equal than 'e'.
        2) py_i_f, where 'i' represents a circuit and 'f' represents a value in [0,l_max].
           i in [0,n], f in [0,l_max].
           py_i_f is True IFF yi≤f. Which means that the y coordinate of the left-bottom corner of circuit 'i' has been placed
           less or equal than 'f'.
        3) lr_i_j, where 'i' and 'j' are two circuits.
           i,j in [0,1].
           lr_i_j is True IFF the circuit 'i' has been placed on the left of the circuit 'j'. 
           Namely, xi+wi≤xj.
        3) ud_i_j, where 'i' and 'j' are two circuits.
           i,j in [0,1].
           ud_i_j is True IFF the circuit 'i' has been placed at the downward to the circuit 'j'. 
           Namely, yi+hi≤yj.

    We encode the fact that two circuits can't overlap in the following way.
    For each pair of circuits 'i' and 'j' (i<j), at least one among {lr_i_j, lr_j_i, ud_i_j, ud_j_i}.
    ('i' is at the left to 'j' or 'j' is at the left to 'i' or 'i' is at the downward to 'j' or 'j' is at the downward to 'i').
    So, we have the constraint:
                           lr_i_j \/ lr_j_i \/ ud_i_j \/ ud_j_i

    Now, for each pair of circuits 'i' and 'j' (i<j), we have to encode the "meaning" of each variable lr_i_j, lr_j_i, 
    ud_i_j, ud_j_i.
    1) If lr_i_j is True, then we have that:
                    xj≤e+wi -> xi≤e,  for each possible 'e'
       which is equivalent to:
                    px_j{e+wi} ->  px_ie,  for each possible 'e'
       which is equivalent to:
                    ¬px_j{e+wi} \/  px_ie,  for each possible 'e'.
       On the whole, we have to add the following constraint:
                ∀e (lr_i_j -> (¬px_j{e+wi} \/  px_ie)).
       Which is equivalent to: 
                ∀e (¬lr_i_j \/ ¬px_j{e+wi} \/  px_ie)
    The same reasoning is applied to lr_j_i, ud_i_j, ud_j_i.
    2) For the variable lr_j_i, we add the constraint
                ∀e (¬lr_j_i \/ ¬px_i{e+wj} \/  px_je).
    3) For the variable ud_i_j, we add the constraint
                ∀f (ud_i_j \/ ¬py_j{f+wi} \/  px_if).
    4) For the variable ud_j_i, we add the constraint
                ∀f (ud_j_i \/ ¬py_i{f+wj} \/  px_jf).

    Finally, we have to put the other constraints about px_ie and py_if for the ordering encoding.
    For each circuit 'i', we have to put:
            ∀e (¬px_ie \/ px_i{e+1})    (which is equivalent to ∀e (px_ie -> px_i{e+1}))
    and
            ∀f (¬py_if \/ py_i{f+1})    (which is equivalent to ∀f (py_if -> py_i{f+1}))
        

    --- SUM UP ---
    The constraints are the following.
    1)  ∀i,j∈[0,n-1]  lr_i_j \/ lr_j_i \/ ud_i_j \/ ud_j_i
    2)  ∀i,j∈[0,n-1] ∀e∈[0,w-1] (¬lr_i_j \/ ¬px_j{e+wi} \/  px_ie)
    3)  ∀i,j∈[0,n-1] ∀e∈[0,w-1] (¬lr_j_i \/ ¬px_i{e+wj} \/  px_je)
    4)  ∀i,j∈[0,n-1] ∀f∈[0,l_max-1] (ud_i_j \/ ¬py_j{f+wi} \/  px_if)
    5)  ∀i,j∈[0,n-1] ∀f∈[0,l_max-1] (ud_j_i \/ ¬py_i{f+wj} \/  px_jf)
    6)  ∀i∈[0,n-1] ∀e∈[0,w-1] (¬px_ie \/ px_i{e+1})
    7)  ∀i∈[0,n-1] ∀f∈[0,l_max-1] (¬py_if \/ py_i{f+1})
    In all these constraints, we consider i!=j.
        

    --- REDUCTIONS AND SYMMETRIES BREAKING ---
    Additional constraints, for reducing the domains and breaking some simmetries.

    A. Group of constraints about the horizontal overlapping: overlapping along the width.
       Constraints 2) and 3).
       If w-wi-wj<0, this means that the circuits 'i'-'j' can't be placed one on the left of the other (the sum of their 
       widths exceed the total width, they don't fit into the plate). In this case, we don't put the constraints 2) and 3), 
       but we simply put: 
                                ¬lr_i_j /\ ¬lr_j_i.
       So, we have:
                                ∀i,j  ,if w-wi-wj<0,  ¬lr_i_j /\ ¬lr_j_i        
       If w-wi-wj>=0, we put the constraints 2) and 3). But we put them only for e∈[0,w-wi-wj]:
                                    2)  ∀i,j ∀e∈[0,w-wi-wj] (¬lr_i_j \/ ¬px_j{e+wi} \/  px_ie)
                                    3)  ∀i,j ∀e∈[0,w-wi-wj] (¬lr_j_i \/ ¬px_i{e+wj} \/  px_je) 
       This because, from w-wi-wj+1 up to w, the circuits 'i'-'j' can't be placed one on the left of the other: they don't 
       fit into the plate.

       If w-wi-wj>=0, we have also other additional constraints.
   
       For the constraint 2) (i.e. for lr_i_j), we have also to explicitely ensure that, if e<wi, then we have
                                    lr_i_j  ->   ¬px_j_e
       which is equivalent to:
                                    ¬lr_i_j \/ ¬px_j_e.
       (The meaning is: when e<wi, if 'i' is placed on the left of 'j', then xj>e).
       So, we add the constraint:
                                    ∀i,j ∀e∈[0,wi] (¬lr_i_j \/ ¬px_j_e)

       This same reasoning is applied for the constraint 3) (i.e. for lr_j_i):
                                    ∀i,j ∀e∈[0,wj] (¬lr_j_i \/ ¬px_i_e)

       To sum up, the constraints 2) and 3) becomes:
            A1) ∀i,j∈[0,n-1] ,if w-wi-wj<0, ¬lr_i_j /\ ¬lr_j_i
            A2) ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,w-wi-wj] (¬lr_i_j \/ ¬px_j{e+wi} \/  px_ie)
            A3) ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,w-wi-wj] (¬lr_j_i \/ ¬px_i{e+wj} \/  px_je)
            A4) ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,wi] (¬lr_i_j \/ ¬px_j_e)
            A5) ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,wj] (¬lr_j_i \/ ¬px_i_e)
       Group A of constraints.
       In all these constraints, we consider i!=j.

    B. Group of constraints about the vertical overlapping: overlapping along the heigth.
       Constraints 4) and 5).
       The exact same reasoning is applied. 
       We obtain the following constraints (group B):
            B1) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ¬ud_i_j /\ ¬ud_j_i
            B2) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,l_max-hi-hj] (¬ud_i_j \/ ¬py_j{f+hi} \/  py_if)
            B3) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,l_max-hi-hj] (¬ud_j_i \/ ¬py_i{h+hj} \/  py_jf)
            B4) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,hi] (¬ud_i_j \/ ¬py_j_f)
            B5) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,hj] (¬ud_j_i \/ ¬py_i_f)
       In all these constraints, we consider i!=j.

    C. Group of general constraints about the semantic of the variables.
       Constraints 6) and 7).
       Regarding the constraint 6), if e∈[w-wi,w-1], we know for sure that xi<e (i.e. px_ie), because that circuit 'i' is 
       for sure placed before 'e'.
       Therefore, we put the constraint:
                                       ∀i ∀e∈[w-wi,w-1] px_ie
       At the same time, we ensure the constraint 6) only for e∈[w-wi-1]:
                                       ∀i ∀e∈[w-wi-1] (¬px_ie \/ px_i{e+1}) 

       We apply the exact same reasoning to the constraint 7).
                                       ∀i ∀f∈[l_max-hi,w-1] py_if
                                       ∀i ∀f∈[l_max-hi-1] (¬py_if \/ py_i{f+1})

       To sum up, the group C of constraints is the following:
            C1) ∀i∈[0,n-1] ∀e∈[w-wi,w-1] px_ie
            C2) ∀i∈[0,n-1] ∀e∈[w-wi-1] (¬px_ie \/ px_i{e+1}) 
            C3) ∀i∈[0,n-1] ∀f∈[l_max-hi,w-1] py_ifs
            C4) ∀i∈[0,n-1] ∀f∈[l_max-hi-1] (¬py_if \/ py_i{f+1}) 
       In all these constraints, we consider i!=j.    
        

    --- FINAL SUM UP ---
    The constraints are the following.
    1)  ∀i,j∈[0,n-1]  lr_i_j \/ lr_j_i \/ ud_i_j \/ ud_j_i
    A1) ∀i,j∈[0,n-1] ,if w-wi-wj<0, ¬lr_i_j /\ ¬lr_j_i
    A2) ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,w-wi-wj] (¬lr_i_j \/ ¬px_j{e+wi} \/  px_ie)
    A3) ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,w-wi-wj] (¬lr_j_i \/ ¬px_i{e+wj} \/  px_je)
    A4) ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,wi] (¬lr_i_j \/ ¬px_j_e)
    A5) ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,wj] (¬lr_j_i \/ ¬px_i_e)
    B1) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ¬ud_i_j /\ ¬ud_j_i
    B2) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,l_max-hi-hj] (¬ud_i_j \/ ¬py_j{f+hi} \/  py_if)
    B3) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,l_max-hi-hj] (¬ud_j_i \/ ¬py_i{h+hj} \/  py_jf)
    B4) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,hi] (¬ud_i_j \/ ¬py_j_f)
    B5) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,hj] (¬ud_j_i \/ ¬py_i_f)
    C1) ∀i∈[0,n-1] ∀e∈[w-wi,w-1] px_ie
    C2) ∀i∈[0,n-1] ∀e∈[w-wi-1] (¬px_ie \/ px_i{e+1}) 
    C3) ∀i∈[0,n-1] ∀f∈[l_max-hi,w-1] py_ifs
    C4) ∀i∈[0,n-1] ∀f∈[l_max-hi-1] (¬py_if \/ py_i{f+1}) 
    In all these constraints, we consider i!=j.

    """
    def __solve(self, l_max):
        """Solves the given VLSI instance, using the SAT encoding 10.

        It is an auxiliary method. Its aim is to solve the VLSI instance without performing optimization: any solution is 
        good.

        Parameters
        ----------
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
                    # Constraints A2) and A3)
                    for e in range(w-dimsX[i]-dimsX[j]+1):
                        s.add( Or(Not(lr[i][j]), px[i][e], Not(px[j][e+dimsX[i]])) )
                        s.add( Or(Not(lr[j][i]), px[j][e], Not(px[i][e+dimsX[j]])) )
                    # Constraint A4)
                    for e in range(dimsX[i]):
                        s.add( Or(Not(lr[i][j]),Not(px[j][e])) )
                    # Constraint A5)
                    for e in range(dimsX[j]):
                        s.add( Or(Not(lr[j][i]),Not(px[i][e])) )
                    
                # Group B
                # Constraint B1)
                if l_max-dimsY[i]-dimsY[j] < 0:
                    s.add( Not(ud[i][j]) )
                    s.add( Not(ud[j][i]) )
                else:
                    # Constraints B2) and B3)
                    for f in range(l_max-dimsY[i]-dimsY[j]+1):
                        s.add( Or(Not(ud[i][j]), py[i][f], Not(py[j][f+dimsY[i]])) )
                        s.add( Or(Not(ud[j][i]), py[j][f], Not(py[i][f+dimsY[j]])) )
                    # Constraint B4)
                    for f in range(dimsY[i]):
                        s.add( Or(Not(ud[i][j]),Not(py[j][f])) )
                    # Constraint B5)
                    for f in range(dimsY[j]):
                        s.add( Or(Not(ud[j][i]),Not(py[i][f])) )

        # Ensure the constraints of the group C)
        for i in range(n):
            # Constraint C1)
            for e in range(w-dimsX[i],w):
                s.add(px[i][e])
            # Constraint C2)
            for e in range(w-dimsX[i]):
                s.add( Or(Not(px[i][e]),px[i][e+1]) )           
            # Constraint C3)
            for f in range(l_max-dimsY[i],l_max):
                s.add(py[i][f])
            # Constraint C4)
            for f in range(l_max-dimsY[i]):
                s.add( Or(Not(py[i][f]),py[i][f+1]) )
                    
        if s.check() != sat:
            raise UnsatError('UNSAT')
        
        return s, px, py


    def __compute_coords(self, s, px, py, l_max):
        """Computes the coords of the rectangles, namely the coordinates of the lower-left verteces of the circuits.

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
        """Solves the given VLSI instance, using the SAT encoding 10.

        It performs optimization: the best solution is found (if any).
        (If this class is used as a parallel process with a time limit, there is not gurantee of founding the optimal 
        solution, but only the best solution found so far).

        The implementation is based on the usage of the `__solve` method.
        Basically, a loop iterating over all the possible solutions is performed, searching for the best possible solution.
        At each iteration, the solver is created and run from scratch, with the current best length of the plate (i.e. `l`) 
        as upper bound for the length of the plate (i.e. `l_max`). (Actually, `l-1` is given as `l_max`).
        In this way, at each iteration a better solution is found.

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

        w_max = max(dimsX)  # The maximum width of a circuit
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

        while True:
            try:
                # Search for a solution, given the maximum l
                s, px, py = self.__solve(l_max)

                # A solution has been found
                first_solution = True

                # Compute the coords (x and y) of the rectangles in the current solution
                coords = self.__compute_coords(s, px, py, l_max)

                # Store the current solution into `self.results`
                self.results['best_coords'] = coords
                self.results['best_l'] = l_max
                # print(l_max)

                # Update `l_max`
                l_max = l_max-1

            except UnsatError:  # Found UNSAT: leave the cycle
                break

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