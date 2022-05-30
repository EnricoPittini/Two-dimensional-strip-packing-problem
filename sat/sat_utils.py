from z3 import *
from itertools import combinations

def at_least_one(B):
    return Or(B)
def at_most_one(B, name=""):
    return And( [Not(And(pair[0], pair[1])) for pair in combinations(B, 2)] )
def exactly_one(B, name=''):
    return And(at_least_one(B), at_most_one(B, name=name))

class UnsatError(BaseException):
    pass

def compute_l(coords, dimsY, n):
    return max([coords[i][1]+dimsY[i] for i in range(n)])