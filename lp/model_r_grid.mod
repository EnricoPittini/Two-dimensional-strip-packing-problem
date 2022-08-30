# MODEL R GRID:
# Grid model based on the position and covering methodology and accounting for rotations.

####### INPUT PARAMETERS
/** The number of the circuits. */
param n integer > 0;
/** The set of circuits. */
set N := 1..n;
/** The set of circuits doubled in order to consider rotations. */
set doubleN := 1..2*n;
/** The width of the plate. */
param w integer > 0;
/** The current minimum length of the plate. */
param l integer >=0;
/** The total number of available positions. */
param nPos integer > 0;
/** The number of cells in the plate. */
param nCells integer > 0;
/** Minimum position id for each circuit. */
param minV {doubleN} integer >=0 <=nPos;
/** Maximum position id for each circuit. */
param maxV {doubleN} integer >=0 <=nPos;
/** Correspondence matrix between the valid positions and the cells occupied in the plate. */
param C {1..nPos, 1..nCells} integer >=0 <=1;

####### VARIABLES
/** Array describing whether a circuit is placed in a valid position. */
var x {doubleN, 1..nPos} integer >=0 <=1;

####### SOLVE
minimize result: 0;

####### SUCH THAT:
# Constrain guaranteeing at most one item is assigned in each cell of the plate.
subject to noOverlap {i in 1..nCells}:
    sum {c in doubleN, j in minV[c]..maxV[c]} C[j,i]*x[c,j] <= 1;

# Constrain guaranteeing all circuits will be inserted in the plate exactly one time considering even their rotation.
subject to insertAll {c1 in N, c2 in n+1..2*n}:
    sum {i in minV[c1]..maxV[c1]} x[c1,i] + sum {j in minV[c2]..maxV[c2]} x[c2,j] = 1;

# Constrain guaranteeing the capacity of the plate will not be exceeded.
subject to notExceed:
    sum {c in doubleN, j in minV[c]..maxV[c], i in 1..nCells} C[j,i]*x[c,j] <= w * l;
