from z3 import *
from itertools import combinations
import multiprocessing
import math    



########## VLSI SAT ABSTRACT

class Vlsi_sat_abstract(multiprocessing.Process):
    """Class for solving the VLSI problem using SAT.

    It inheriths from `multiprocessing.Process`, in order to be executable as parallel process.
    The typical usage is to run this process in parallel using a certain time limit. In such case, if the time limit exceed,
    the user is not guaranteed to get an optimal solution, but only the best solution found so far.

    It is a general class, it is not a specific encoding.
    It collects the basic common attributes and properties, shared among the different SAT encodings. 
    A SAT encoding class inherits from this class.

    Attributes
    ----------
    w : int
        The width of the plate
    n : int
        The number of circuits
    dimsX : list of int
        Dims X (i.e. width) of the circuits
    dimsY : list of int
        Dims Y (i.e. height) of the circuits
    results : dict
        Dictionary containing the results. It contains three elements.
            1. results['best_coords'] : list of tuples of int
               List containing the coordX and coordY of the lower-left vertex of each circuit in the best solution.
            2. results['best_l'] : int
               Length of the plate in the best solution.
            3. results['finish'] : bool
               Boolean flag saying whether the solving has finished or not.
               (This is useful in particular if this class is run as parallel process with a time limit).
            4. results['unsat'] : bool
               Boolean flag saying whether the problem is UNSAT or not.
               (For proving that the problem is UNSAT, the solving process must have finishe, therefore results['finish'] 
               must be True).
    
    Notes
    -----
    The way the user and the `Vlsi_sat` class instance communicate is through the `results` dictionary. It is given to the
    class constructor and it is stored inside the class: then, it is modified by injecting the solution (this each time a 
    better solution is found).

    """

    def __init__(self, w, n, dims, results):
        super().__init__()

        self.w = w
        self.n = n 
        self.dimsX = [dims[i][0] for i in range(n)]
        self.dimsY = [dims[i][1] for i in range(n)]

        self.results = results
        self.results['best_coords'] = None
        self.results['best_l'] = None
        self.results['finish'] = False
        self.results['unsat'] = False



########## AT LEAST ONE ENCODING
def at_least_one(B):
    return Or(B)



########## AT MOST ONE ENCODINGS
def at_most_one(B, encoding='sequential', name=''):
    if encoding=='pairwise':
        return at_most_one_PAIRWISE(B, name)
    elif encoding=='sequential':
        return at_most_one_SEQUENTIAL(B, name)
    elif encoding=='bitwise':
        return at_most_one_BITWISE(B, name)
    elif encoding=='heule':
        return at_most_one_HEULE(B, name)
    elif encoding=='commander':
        return at_most_one_COMMANDER(B, name)
    elif encoding=='bimander':
        return at_most_one_BIMANDER(B, name)

def at_most_one_PAIRWISE(B, name=''):
    return And( [Not(And(pair[0], pair[1])) for pair in combinations(B, 2)] )
    
def at_most_one_SEQUENTIAL(B, name):
    # List which will contain all the formulas for the at_most_one constraint
    formulas_list = []
    
    n = len(B)  # Number of variables
    
    # Defining the new variables (Note: the indeces start from 0)
    s = [Bool(f's_{name}_{i}') for i in range(n-1)]
    
    # LET'S ADD THE FORMULAS, ONE AT A TIME
    
    # First formula
    formulas_list.append( Or(Not(B[0]), s[0]) )
    
    # Second formula
    formulas_list.append( Or(Not(B[n-1]), Not(s[n-2])) )
    
    # Third big formula
    for i in range(1, n-1):
        formula = And( Or(Not(B[i]),s[i]), Or(Not(s[i-1]),s[i]), Or(Not(B[i]),Not(s[i-1])) )
        formulas_list.append(formula)
        
    # Return the conjunction among all the added formulas
    return And(formulas_list)

def to_binary(n, length):
    """
    Returns the binary representation of given the number `n`, using `length` bits.
    
    This binary representation is a list, in which each element is a bit: either 0/1. Actually, each bit is a string: 
    either "0"/"1"
    
    """
    n_binary = bin(n).split("b")[-1]
    if length:
        return "0"*(length - len(n_binary)) + n_binary
    return n_binary

def at_most_one_BITWISE(B, name):
    # List which will contain all the formulas for the at_most_one constraint
    formulas_list = []
    
    n = len(B)  # Number of variables
    
    m = math.ceil(math.log2(n))  # Number of new variables
    
    # Defining the new variables (Note: the indeces start from 0)
    r = [Bool(f'r_{name}_{i}') for i in range(m)]
    
    # LET'S ADD THE FORMULAS, ONE AT A TIME
    
    # Iterate over all the variables B_0, ..., B_{n-1}. For each variable, a formula must be added
    for i in range(n):
        # The current variable is B_i
        
        # Binary representation of 'i' (using m bits)
        binary_representation = to_binary(i, m)
        
        # Let's build the big AND formula. Big logical and: /\ phi.        
        big_and_formula = And( [(r[j] if (binary_representation[j]=="1") else Not(r[j])) for j in range(m)] )
        
        # Equivalent construction of 'big_and_formula'
        # big_and_formula = []
        # for j in range(m):
        #     phi = r[j] if (binary_representation[j]=="1") else Not(r[j])
        #     big_and_formula.append(phi)
        # big_and_formula = And(big_and_formula)
        
        # This is the overall formula to add for the current variable B_i
        formula = Or(Not(B[i]), big_and_formula)
        
        formulas_list.append(formula)
        
    # Return the conjunction among all the added formulas    
    return And(formulas_list)

def at_most_one_HEULE(B, name):  
    n = len(B)  # Number of variables
    
    if n<=4: 
        # BASE CASE: n<=4
        return at_most_one_PAIRWISE(B)
    
    # RECURSIVE CASE: n>4
    
    # New variable
    y = Bool(f'y_{name}')
    
    # First group of variables
    first_group = B[:3] + [y]
    
    # Second group of variables
    second_group = [Not(y)] + B[3:]
    
    # Return the conjunction between the recursive calls applied on the two groups 
    return And( at_most_one_HEULE(first_group, name=name), at_most_one_HEULE(second_group, name=name+'_') )

def at_most_one_COMMANDER(B, name, m=None):
    # print('HI')
    n = len(B)
    
    if not m:  # Case in which we fix the number of variables in each group
        g = 4  # Number of variables in each group (Fixed)
        m = math.ceil(n/g)  # Number of groups (Computed)
        base_case = n <= g
    else:  # Case in which the number of groups is given (FIxed)
        g = math.ceil(n/m)  # Number of variables in each group (Computed)
        base_case = n <= m
        
    if base_case:
        return at_most_one_PAIRWISE(B, name=name)
        
    Gs = []
    for i in range(m):
        if i!=m-1:
            Gs.append(B[g*i:g*(i+1)])
        else:
            Gs.append(B[g*i:])
        
    c = [Bool(f'c_{name}_{i}') for i in range(m)]
    
    formula1 = []
    for i in range(m):
        formula1.append(exactly_one(Gs[i] + [Not(c[i])], encoding='pairwise', name=name))
    formula1 = And(formula1)
    
    # print(c)
    formula2 = at_most_one_COMMANDER(c, name=name+"_")
    
    return And(formula1, formula2) 

def at_most_one_BIMANDER(B, name, m=None):
    # print('HI')
    n = len(B)
    
    if not m:
        g = 4
        m = math.ceil(n/g)
        #base_case = n <= g
    else:
        g = math.ceil(n/m)
        #base_case = n <= m
        
    #if base_case:
    #    return at_most_one_NAIVE(B, name=name)
        
    Gs = []
    for i in range(m):
        if i!=m-1:
            Gs.append(B[g*i:g*(i+1)])
        else:
            Gs.append(B[g*i:])
        
    #c = [Bool(f'c_{name}_{i}') for i in range(m)]
    r = math.ceil(math.log2(m))
    b = [Bool(f'b_{name}_{i}') for i in range(r)]
    
    formula1 = []
    for i in range(m):
        formula1.append(at_most_one_PAIRWISE(Gs[i], name=name))
    formula1 = And(formula1)
    
    # print(c)
    formula2 = []
    for i in range(m):
        binary_representation = to_binary(i, r)
        #print(binary_representation)
        for h in range(len(Gs[i])):  # g
            for j in range(r):
                #phi = b[j] if (binary_representation[j]=="1") else Not(b[j])
                formula2.append( Or(Not(Gs[i][h]),b[j] if (binary_representation[j]=="1") else Not(b[j])) )
    formula2 = And(formula2)
    
    return And(formula1, formula2)  



########## EXACTLY ONE ENCODING
def exactly_one(B, encoding='sequential', name=''):
    return And(at_least_one(B), at_most_one(B, encoding=encoding, name=name))




    

class UnsatError(BaseException):
    pass

# TODO
"""class TimeoutError(BaseException):
    pass"""

# TODO move to encoding_0 and encoding_1 (it is used only by them)
def compute_l(coords, dimsY, n):
    return max([coords[i][1]+dimsY[i] for i in range(n)])