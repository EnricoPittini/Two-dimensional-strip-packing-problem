from z3 import *
from itertools import combinations

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

def compute_l(coords, dimsY, n):
    return max([coords[i][1]+dimsY[i] for i in range(n)])