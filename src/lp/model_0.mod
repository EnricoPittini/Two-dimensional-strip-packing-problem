# MODEL 0:
# First base interpretation of the problem. 

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

####### VARIABLES
/** X coordinate of the bottom-left corner of the circuits. */
var coordsX {N} integer >=0 <=w;
/** Y coordinate of the bottom-left corner of the circuits. */
var coordsY {N} integer >=0;
/** Binary variables for each coordinate i,j related to the non-overlapping constraints. */
var b {N,N,1..4} integer >=0 <=1;
/** The length of the plate. */
var l integer >= 0;

####### SOLVE
minimize result: l;

####### SUCH THAT:
# Constraints guaranteeing that all the circuits are within the bound of the plate.
subject to boundX {i in N}:
	coordsX[i]+dimsX[i]<= w;
subject to boundY {i in N}:
	coordsY[i]+dimsY[i]<= l;

# No-overlapping constraints:
# If a constraint is active b[i,j,k] = 1 then the circuits must not overlap in the given dimension.
# Otherwise (the constraint is not active b[i,j,k] = 0), the constraint will always be satisfied thanks to the Big-M 
# technique and the overlapping in the given dimension will be ignored.
subject to noOverlapX1 {i in N, j in 1..i-1}:
	coordsX[i]+dimsX[i]<= coordsX[j]+ 10000*(1 - b[i,j,1]);
subject to noOverlapX2 {i in N, j in 1..i-1}:
	coordsX[j]+dimsX[j]<= coordsX[i]+ 10000*(1 - b[i,j,3]);
subject to noOverlapY1 {i in N, j in 1..i-1}:
	coordsY[i]+dimsY[i]<= coordsY[j]+ 10000*(1 - b[i,j,2]);
subject to noOverlapY2 {i in N, j in 1..i-1}:
	coordsY[j]+dimsY[j]<= coordsY[i]+ 10000*(1 - b[i,j,4]);

# At most one vertical or horizontal relation should be implied.
subject to oneOnlyX {i in N, j in 1..i-1}:
	b[i,j,1] + b[i,j,3] <= 1;
subject to oneOnlyY {i in N, j in 1..i-1}:
	b[i,j,2] + b[i,j,4] <= 1;

# At least one of the above constraint must be active (not relaxed) for all the coordinates i,j.
subject to overlapActivation {i in N, j in 1..i-1}:
	b[i,j,1] + b[i,j,2] + b[i,j,3] + b[i,j,4] >= 1;
