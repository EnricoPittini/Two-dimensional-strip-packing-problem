from z3 import *
from itertools import combinations
import multiprocessing    


class Vlsi_sat_abstract(multiprocessing.Process):
    """Class for solving the VLSI problem using SAT.

    It inheriths from `multiprocessing.Process`, in order to be executable as parallel process.
    The typical usage is to run this process in parallel using a certain time limit. In such case, if the time limit exceed,
    the user is not guaranteed to get an optimal solution, but only the best solution found so far.

    If the problem is UNSAT, the `UnsatError` exception is raised.

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
               (This is useful in particular if this class is run as parallel process).
    
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


def at_least_one(B):
    return Or(B)
def at_most_one(B, name=''):
    # return And( [Not(And(pair[0], pair[1])) for pair in combinations(B, 2)] )
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
def exactly_one(B, name=''):
    return And(at_least_one(B), at_most_one(B, name=name))

class UnsatError(BaseException):
    pass

# TODO
"""class TimeoutError(BaseException):
    pass"""

# TODO move to encoding_0 and encoding_1 (it is used only by them)
def compute_l(coords, dimsY, n):
    return max([coords[i][1]+dimsY[i] for i in range(n)])