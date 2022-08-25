# MODEL 1:
# Improvement of the base model, optimization on the dimension of the variables and bounds for the length of the plate. 

####### INPUT PARAMETERS
/** The number of the circuits. */
param n integer > 0;
/** The set of circuits. */
set N := 1..n;
/** The width of the plate. */
param w integer > 0;
/** Widths of the circuits. */
param dimsX {N} integer >0 <=w;
/** Heights of the circuits. */
param dimsY {N} integer >0;
/** The current minimum length of the plate. */
param l integer >=0;
/** The total number of available positions. */
param nPos integer > 0;
/** The number of cells in the plate. */
param nCells integer > 0;
/** Position ids for each circuit. */
param V {0..n} integer >=0 <=nPos;
/** Array of valid positions. */
param C {1..nPos, 1..nCells} integer >=0 <=1;

####### VARIABLES
/** Array describing whether a circuit is placed in a valid position. */
var x {N, 1..nPos} integer >=0 <=1;

####### SOLVE
minimize result: 0;

####### SUCH THAT:
# Constrain guaranteeing at most one item is assigned in each cell of the plate.
subject to noOverlap {i in 1..nCells}:
    sum {c in N, j in V[c-1]+1..V[c]} C[j,i]*x[c,j] <= 1;

# Constrain guaranteeing all circuits will be inserted in the plate exactly one time.
subject to insertAll {c in N}:
    sum {j in V[c-1]+1..V[c]} x[c,j] = 1;
# Constrain guaranteeing a circuits will not be inserted in an invalid position.
subject to notValidBefore {c in N}:
    sum {j in 1..V[c-1]} x[c,j] = 0;
subject to notValidAfter {c in N}:
    sum {j in V[c]+1..V[n]} x[c,j] = 0;

# Constrain guaranteeing the capacity of the strip will not be exceeded.
subject to notExceed:
    sum {c in N, j in V[c-1]+1..V[c], i in 1..nCells} C[j,i]*x[c,j] <= w * l;
