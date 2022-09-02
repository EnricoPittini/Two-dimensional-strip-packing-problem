from z3 import *
from sat_utils import UnsatError, Vlsi_sat_abstract


class Vlsi_sat(Vlsi_sat_abstract):
    """Class for solving the VLSI problem in SAT, using the encoding 11.

    It inherits from the class `Vlsi_sat_abstract`.

    This encodings solves a different variant of the VLSI problem: variant in which rotation is allowed. Each circuit can be 
    rotated by 90°, swapping the width (i.e. dimsX) with the height (i.e. dimsY) of the circuit.

    For making this encoding, the encoding 10 has been taken and then modified: basically, this encoding is a modification
    of the encoding found in the paper *'A SAT-based Method for Solving the Two-dimensional Strip Packing Problem'* (i.e. 
    order encoding).
    Below the encoding is described.

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


    --- MODIFICATION OF THE ENCODING 10 (I.E. ORDER ENCODING) ---
    First of all, a new set of variables is defined.
    r_i, where 'i' represents a circuit. i in [0,n].
    r_i is True IFF the 'i'-th rectangle has been rotated, meaning that wi and hi have been swapped.

    Using these new variables, the constraints are modified, taking into account the possibility of rotating the circuits.
        
    1)  ∀i,j∈[0,n-1]  lr_i_j \/ lr_j_i \/ ud_i_j \/ ud_j_i
        This contraint reamins the same.

    First of all, group A) of constraints.

    A1) ∀i,j∈[0,n-1] ,if w-wi-wj<0, ¬lr_i_j /\ ¬lr_j_i
        We have to modify the constraint '¬lr_i_j /\ ¬lr_j_i', by imposing that this is True only if both rectangles have not
        been rotated. We have:
                            (¬r_i /\ ¬r_j -> ¬lr_i_j) /\ (¬r_i /\ ¬r_j -> ¬lr_j_i)
        Which is equivalent to:
                            (r_i \/ r_j \/ ¬lr_i_j) /\ (r_i \/ r_j \/ ¬lr_j_i)
        On the whole: ∀i,j∈[0,n-1] ,if w-wi-wj<0, (r_i \/ r_j \/ ¬lr_i_j) /\ (r_i \/ r_j \/ ¬lr_j_i)
        This is only about a single possibility: both the circuits 'i' and 'j' are not rotated. We have three other 
        combinations.
            - 'j' is rotated, while 'i' not.
               ∀i,j∈[0,n-1] ,if w-wi-hj<0, (r_i \/ ¬r_j \/ ¬lr_i_j) /\ (r_i \/ ¬r_j \/ ¬lr_j_i)
            - 'i' is rotated, while 'j' not.
               ∀i,j∈[0,n-1] ,if w-hi-wj<0, (¬r_i \/ r_j \/ ¬lr_i_j) /\ (¬r_i \/ r_j \/ ¬lr_j_i)
            - 'i' and 'j' are both rotated.
               ∀i,j∈[0,n-1] ,if w-hi-wj<0, (¬r_i \/ ¬r_j \/ ¬lr_i_j) /\ (¬r_i \/ ¬r_j \/ ¬lr_j_i)

    A2) ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,w-wi-wj] (¬lr_i_j \/ ¬px_j{e+wi} \/  px_ie)
        We have to modify the constraint (¬lr_i_j \/ ¬px_j{e+wi} \/  px_ie), by imposing that this is True only if both 
        rectangles have not been rotated. We have:
                           (r_i \/ r_j \/ ¬lr_i_j \/ ¬px_j{e+wi} \/  px_ie)
        (this is obtained from the implication (¬r_i /\ ¬r_j -> ...) , as seen before).
        So:  ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,w-wi-wj] (r_i \/ r_j \/ ¬lr_i_j \/ ¬px_j{e+wi} \/  px_ie)
        This is only about a single possibility: both the circuits 'i' and 'j' are not rotated. We have three other 
        combinations.
            - 'j' is rotated, while 'i' not.
               ∀i,j∈[0,n-1] ,if w-wi-hj>=0, ∀e∈[0,w-wi-hj] (r_i \/ ¬r_j \/ ¬lr_i_j \/ ¬px_j{e+wi} \/  px_ie)
            - 'i' is rotated, while 'j' not.
               ∀i,j∈[0,n-1] ,if w-hi-wj>=0, ∀e∈[0,w-hi-wj] (¬r_i \/ r_j \/ ¬lr_i_j \/ ¬px_j{e+hi} \/  px_ie)
            - 'i' and 'j' are both rotated.
               ∀i,j∈[0,n-1] ,if w-hi-hj>=0, ∀e∈[0,w-hi-hj] (¬r_i \/ ¬r_j \/ ¬lr_i_j \/ ¬px_j{e+hi} \/  px_ie)

    A3) ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,w-wi-wj] (¬lr_j_i \/ ¬px_i{e+wj} \/  px_je)
        Same modification of A2, but in which 'i' and 'j' are swapped.
            - 'i' and 'j' are both not rotated.
               ∀i,j∈[0,n-1] ,if w-wi-hj>=0, ∀e∈[0,w-wi-wj] (r_i \/ r_j \/ ¬lr_j_i \/ ¬px_i{e+wj} \/  px_je)
            - 'j' is rotated, while 'i' not.
               ∀i,j∈[0,n-1] ,if w-wi-hj>=0, ∀e∈[0,w-wi-hj] (r_i \/ ¬r_j \/ ¬lr_j_i \/ ¬px_i{e+hj} \/  px_je)
            - 'i' is rotated, while 'j' not.
               ∀i,j∈[0,n-1] ,if w-hi-wj>=0, ∀e∈[0,w-hi-wj] (¬r_i \/ r_j \/ ¬lr_j_i \/ ¬px_i{e+wj} \/  px_je)
            - 'i' and 'j' are both rotated.
               ∀i,j∈[0,n-1] ,if w-hi-hj>=0, ∀e∈[0,w-hi-hj] (¬r_i \/ ¬r_j \/ ¬lr_j_i \/ ¬px_i{e+hj} \/  px_je)

    A4) ∀i,j∈[0,n-1] ∀e∈[0,wi] (¬lr_i_j \/ ¬px_j_e)
        This remains True only if the circuit 'i' has not been rotated. Therefore, we need to modify the constraint as 
        follows:
                        ∀i,j∈[0,n-1] ∀e∈[0,wi] (r_i \/ ¬lr_i_j \/ ¬px_j_e)
        (Same reasoning of before, from the implication)
        We add this same constraint also for the case in which the circuit 'i' has been rotated.
                        ∀i,j∈[0,n-1] ∀e∈[0,hi] (¬r_i \/ ¬lr_i_j \/ ¬px_j_e)

    A5) ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,wj] (¬lr_j_i \/ ¬px_i_e)
        Same modification seen in A4, but in which 'i' and 'j' are swapped.
            - ∀i,j∈[0,n-1] ∀e∈[0,wj] (r_j \/ ¬lr_j_i \/ ¬px_i_e)
            - ∀i,j∈[0,n-1] ∀e∈[0,hj] (¬r_i \/¬lr_j_i \/ ¬px_i_e)

    Regarding the constraints of the group B), we apply the same modifications, but working along the vertical axis instead of
    the horizontal one. 

    B1) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ¬ud_i_j /\ ¬ud_j_i
        It becomes the following four constraints:
            - 'i' and 'j' are both not rotated.
               ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, (r_i \/ r_j \/ ¬ud_i_j) /\ (r_i \/ r_j \/ ¬ud_j_i)
            - 'j' is rotated, while 'i' not.
               ∀i,j∈[0,n-1] ,if l_max-hi-wj<0, (r_i \/ ¬r_j \/ ¬ud_i_j) /\ (r_i \/ ¬r_j \/ ¬ud_j_i)
            - 'i' is rotated, while 'j' not.
               ∀i,j∈[0,n-1] ,if l_max-wi-hj<0, (¬r_i \/ r_j \/ ¬ud_i_j) /\ (¬r_i \/ r_j \/ ¬ud_j_i)
            - 'i' and 'j' are both rotated.
               ∀i,j∈[0,n-1] ,if l_max-wi-wj<0, (¬r_i \/ ¬r_j \/ ¬ud_i_j) /\ (¬r_i \/ ¬r_j \/ ¬ud_j_i)

    B2) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,l_max-hi-hj] (¬ud_i_j \/ ¬py_j{f+hi} \/  py_if)
        It becomes the following four constraints:
            - 'i' and 'j' are both not rotated.
               ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,l_max-hi-hj] (r_i \/ r_j \/ ¬ud_i_j \/ ¬py_j{f+hi} \/  py_if)
            - 'j' is rotated, while 'i' not.
               ∀i,j∈[0,n-1] ,if l_max-hi-wj<0, ∀f∈[0,l_max-hi-wj] (r_i \/ ¬r_j \/ ¬ud_i_j \/ ¬py_j{f+hi} \/  py_if)
            - 'i' is rotated, while 'j' not.
               ∀i,j∈[0,n-1] ,if l_max-wi-hj<0, ∀f∈[0,l_max-wi-hj] (¬r_i \/ r_j \/ ¬ud_i_j \/ ¬py_j{f+wi} \/  py_if)
            - 'i' and 'j' are both rotated.
               ∀i,j∈[0,n-1] ,if l_max-wi-wj<0, ∀f∈[0,l_max-wi-wj] (¬r_i \/ ¬r_j \/ ¬ud_i_j \/ ¬py_j{f+wi} \/  py_if)

    B3) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,l_max-hi-hj] (¬ud_j_i \/ ¬py_i{h+hj} \/  py_jf)
        It becomes the following four constraints:
            - 'i' and 'j' are both not rotated.
               ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,l_max-hi-hj] (r_i \/ r_j \/ ¬ud_j_i \/ ¬py_i{h+hj} \/  py_jf)
            - 'j' is rotated, while 'i' not.
               ∀i,j∈[0,n-1] ,if l_max-hi-wj<0, ∀f∈[0,l_max-hi-wj] (r_i \/ ¬r_j \/ ¬ud_j_i \/ ¬py_i{h+wj} \/  py_jf)
            - 'i' is rotated, while 'j' not.
               ∀i,j∈[0,n-1] ,if l_max-wi-hj<0, ∀f∈[0,l_max-wi-hj] (¬r_i \/ r_j \/ ¬ud_j_i \/ ¬py_i{h+hj} \/  py_jf)
            - 'i' and 'j' are both rotated.
               ∀i,j∈[0,n-1] ,if l_max-wi-wj<0, ∀f∈[0,l_max-wi-wj] (¬r_i \/ ¬r_j \/ ¬ud_j_i \/ ¬py_i{h+wj} \/  py_jf)

    B4) ∀i,j∈[0,n-1] ∀f∈[0,hi] (¬ud_i_j \/ ¬py_j_f)
        It becomes the following two contraints:
            - The circuit 'i' has not been rotated.
              ∀i,j∈[0,n-1] ∀f∈[0,hi] (r_i \/ ¬ud_i_j \/ ¬py_j_f)
            - The circuit 'i' has been rotated.
              ∀i,j∈[0,n-1] ∀f∈[0,wi] (¬r_i \/ ¬ud_i_j \/ ¬py_j_f)

    B5) ∀i,j∈[0,n-1] ∀f∈[0,hj] (¬ud_j_i \/ ¬py_i_f)
        It becomes the following two contraints:
            - The circuit 'j' has not been rotated. 
              ∀i,j∈[0,n-1] ∀f∈[0,hj] (r_j \/ ¬ud_j_i \/ ¬py_i_f)
            - The circuit 'j' has not been rotated. 
              ∀i,j∈[0,n-1] ∀f∈[0,wj] (¬r_j \/ ¬ud_j_i \/ ¬py_i_f)

    Finally, group C) of constraints.

    C1) ∀i∈[0,n-1] ∀e∈[w-wi,w-1] px_ie
        This is True, but only if the circuit 'i' has not been rotated. Therefore, it becomes:
                        ∀i∈[0,n-1] ∀e∈[w-wi,w-1] (r_i \/ px_ie)
        We have also to add the case in which the circuit 'i' has been rotated.
                        ∀i∈[0,n-1] ∀e∈[w-hi,w-1] (¬r_i \/ px_ie)

    C2) ∀i∈[0,n-1] ∀e∈[w-wi-1] (¬px_ie \/ px_i{e+1}) 
        It simply becomes: 
                        ∀i∈[0,n-1] ∀e∈[w-1] (¬px_ie \/ px_i{e+1})

    C3) ∀i∈[0,n-1] ∀f∈[l_max-hi,w-1] py_if
        Same modification of C1. It becomes the following two constraints:
                - The circuit 'i' has not been rotated.
                  ∀i∈[0,n-1] ∀f∈[l_max-hi,w-1] (r_i \/ py_if)
                - The circuit 'i' has been rotated.
                  ∀i∈[0,n-1] ∀f∈[l_max-wi,w-1] (¬r_i \/ py_if)

    C4) ∀i∈[0,n-1] ∀f∈[l_max-hi-1] (¬py_if \/ py_i{f+1})
        It simply becomes:  
                        ∀i∈[0,n-1] ∀f∈[l_max-1] (¬py_if \/ py_i{f+1})

    --- FINAL SUM UP ---
    The constraints are the following.
    1)  ∀i,j∈[0,n-1]  lr_i_j \/ lr_j_i \/ ud_i_j \/ ud_j_i
    A1) ∀i,j∈[0,n-1] ,if w-wi-wj<0, (r_i \/ r_j \/ ¬lr_i_j) /\ (r_i \/ r_j \/ ¬lr_j_i)
        ∀i,j∈[0,n-1] ,if w-wi-hj<0, (r_i \/ ¬r_j \/ ¬lr_i_j) /\ (r_i \/ ¬r_j \/ ¬lr_j_i)
        ∀i,j∈[0,n-1] ,if w-hi-wj<0, (¬r_i \/ r_j \/ ¬lr_i_j) /\ (¬r_i \/ r_j \/ ¬lr_j_i)
        ∀i,j∈[0,n-1] ,if w-hi-wj<0, (¬r_i \/ ¬r_j \/ ¬lr_i_j) /\ (¬r_i \/ ¬r_j \/ ¬lr_j_i)
    A2) ∀i,j∈[0,n-1] ,if w-wi-wj>=0, ∀e∈[0,w-wi-wj] (r_i \/ r_j \/ ¬lr_i_j \/ ¬px_j{e+wi} \/  px_ie)
        ∀i,j∈[0,n-1] ,if w-wi-hj>=0, ∀e∈[0,w-wi-hj] (r_i \/ ¬r_j \/ ¬lr_i_j \/ ¬px_j{e+wi} \/  px_ie)
        ∀i,j∈[0,n-1] ,if w-hi-wj>=0, ∀e∈[0,w-hi-wj] (¬r_i \/ r_j \/ ¬lr_i_j \/ ¬px_j{e+hi} \/  px_ie)
        ∀i,j∈[0,n-1] ,if w-hi-hj>=0, ∀e∈[0,w-hi-hj] (¬r_i \/ ¬r_j \/ ¬lr_i_j \/ ¬px_j{e+hi} \/  px_ie)
    A3) ∀i,j∈[0,n-1] ,if w-wi-hj>=0, ∀e∈[0,w-wi-wj] (r_i \/ r_j \/ ¬lr_j_i \/ ¬px_i{e+wj} \/  px_je)
        ∀i,j∈[0,n-1] ,if w-wi-hj>=0, ∀e∈[0,w-wi-hj] (r_i \/ ¬r_j \/ ¬lr_j_i \/ ¬px_i{e+hj} \/  px_je)
        ∀i,j∈[0,n-1] ,if w-hi-wj>=0, ∀e∈[0,w-hi-wj] (¬r_i \/ r_j \/ ¬lr_j_i \/ ¬px_i{e+wj} \/  px_je)
        ∀i,j∈[0,n-1] ,if w-hi-hj>=0, ∀e∈[0,w-hi-hj] (¬r_i \/ ¬r_j \/ ¬lr_j_i \/ ¬px_i{e+hj} \/  px_je)
    A4) ∀i,j∈[0,n-1] ∀e∈[0,wi] (r_i \/ ¬lr_i_j \/ ¬px_j_e)
        ∀i,j∈[0,n-1] ∀e∈[0,hi] (¬r_i \/ ¬lr_i_j \/ ¬px_j_e)
    A5) ∀i,j∈[0,n-1] ∀e∈[0,wj] (r_j \/ ¬lr_j_i \/ ¬px_i_e)
        ∀i,j∈[0,n-1] ∀e∈[0,hj] (¬r_i \/¬lr_j_i \/ ¬px_i_e)
    B1) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, (r_i \/ r_j \/ ¬ud_i_j) /\ (r_i \/ r_j \/ ¬ud_j_i)
        ∀i,j∈[0,n-1] ,if l_max-hi-wj<0, (r_i \/ ¬r_j \/ ¬ud_i_j) /\ (r_i \/ ¬r_j \/ ¬ud_j_i)
        ∀i,j∈[0,n-1] ,if l_max-wi-hj<0, (¬r_i \/ r_j \/ ¬ud_i_j) /\ (¬r_i \/ r_j \/ ¬ud_j_i)
        ∀i,j∈[0,n-1] ,if l_max-wi-wj<0, (¬r_i \/ ¬r_j \/ ¬ud_i_j) /\ (¬r_i \/ ¬r_j \/ ¬ud_j_i)
    B2) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,l_max-hi-hj] (r_i \/ r_j \/ ¬ud_i_j \/ ¬py_j{f+hi} \/  py_if)
        ∀i,j∈[0,n-1] ,if l_max-hi-wj<0, ∀f∈[0,l_max-hi-wj] (r_i \/ ¬r_j \/ ¬ud_i_j \/ ¬py_j{f+hi} \/  py_if)
        ∀i,j∈[0,n-1] ,if l_max-wi-hj<0, ∀f∈[0,l_max-wi-hj] (¬r_i \/ r_j \/ ¬ud_i_j \/ ¬py_j{f+wi} \/  py_if)
        ∀i,j∈[0,n-1] ,if l_max-wi-wj<0, ∀f∈[0,l_max-wi-wj] (¬r_i \/ ¬r_j \/ ¬ud_i_j \/ ¬py_j{f+wi} \/  py_if)
    B3) ∀i,j∈[0,n-1] ,if l_max-hi-hj<0, ∀f∈[0,l_max-hi-hj] (r_i \/ r_j \/ ¬ud_j_i \/ ¬py_i{h+hj} \/  py_jf)
        ∀i,j∈[0,n-1] ,if l_max-hi-wj<0, ∀f∈[0,l_max-hi-wj] (r_i \/ ¬r_j \/ ¬ud_j_i \/ ¬py_i{h+wj} \/  py_jf)
        ∀i,j∈[0,n-1] ,if l_max-wi-hj<0, ∀f∈[0,l_max-wi-hj] (¬r_i \/ r_j \/ ¬ud_j_i \/ ¬py_i{h+hj} \/  py_jf)
        ∀i,j∈[0,n-1] ,if l_max-wi-wj<0, ∀f∈[0,l_max-wi-wj] (¬r_i \/ ¬r_j \/ ¬ud_j_i \/ ¬py_i{h+wj} \/  py_jf)
    B4) ∀i,j∈[0,n-1] ∀f∈[0,hi] (r_i \/ ¬ud_i_j \/ ¬py_j_f)
        ∀i,j∈[0,n-1] ∀f∈[0,wi] (¬r_i \/ ¬ud_i_j \/ ¬py_j_f)
    B5) ∀i,j∈[0,n-1] ∀f∈[0,hj] (r_j \/ ¬ud_j_i \/ ¬py_i_f)
        ∀i,j∈[0,n-1] ∀f∈[0,wj] (¬r_j \/ ¬ud_j_i \/ ¬py_i_f)
    C1) ∀i∈[0,n-1] ∀e∈[w-wi,w-1] (r_i \/ px_ie)
        ∀i∈[0,n-1] ∀e∈[w-hi,w-1] (¬r_i \/ px_ie)
    C2) ∀i∈[0,n-1] ∀e∈[w-1] (¬px_ie \/ px_i{e+1})
    C3) ∀i∈[0,n-1] ∀f∈[l_max-hi,w-1] (r_i \/ py_if)
        ∀i∈[0,n-1] ∀f∈[l_max-wi,w-1] (¬r_i \/ py_if)
    C4) ∀i∈[0,n-1] ∀f∈[l_max-1] (¬py_if \/ py_i{f+1})
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
                    
        if s.check() != sat:
            raise UnsatError('UNSAT')
        
        return s, px, py, r


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
            Actual vertical dimensions of the circuits, after their possible rotation.

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

        # Compute the upper bound for the length of the plate
        max_dim = max(dimsX + dimsY)
        min_rects_per_row = w // max_dim 
        if min_rects_per_row<2:
            l_max = sum([max([dimsX[i],dimsY[i]]) for i in range(n)])
        else:
            sorted_dims = sorted([max([dimsX[i],dimsY[i]]) for i in range(n)], reverse=True)
            l_max = sum([sorted_dims[i] for i in range(n) if i % min_rects_per_row == 0])

        # Boolean flag reprenting if a first solution has already been found
        first_solution = False

        while True:
            try:
                # Search for a solution, given the maximum l
                s, px, py, r = self.__solve(l_max)

                # A solution has been found
                first_solution = True

                # Compute the coords (x and y) and the actual dimensions of the rectangles in the current solution
                coords, actual_dimsX, actual_dimsY = self.__compute_coords_actualDims(s, px, py, r, l_max)

                # Store the current solution into `self.results`
                self.results['best_coords'] = coords
                self.results['best_l'] = l_max
                self.results['actual_dimsX'] = actual_dimsX
                self.results['actual_dimsY'] = actual_dimsY
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