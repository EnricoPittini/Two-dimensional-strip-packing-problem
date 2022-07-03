# MODEL 2A:
# First simmetry breaking approach. 


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

####### DERIVED PARAMETERS
/** Upper bound for the length of the plate. */
param lMax = sum {i in N} dimsY[i];

####### VARIABLES
/** X coordinate of the bottom-left corner of the circuits. */
var coordsX {N} integer >=0 <=w;
/** Y coordinate of the bottom-left corner of the circuits. */
var coordsY {N} integer >=0;
/** Binary variables for each coordinate i,j related to the non-overlapping constraints. */
var b {N,N,1..2} integer >=0 <=1;
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
	coordsX[i]+dimsX[i]<= coordsX[j]+ w*(1 - b[i,j,1]);
subject to noOverlapX2 {i in N, j in 1..i-1}:
	coordsX[j]+dimsX[j]<= coordsX[i]+ w*(1 - b[j,i,1]);
subject to noOverlapY1 {i in N, j in 1..i-1}:
	coordsY[i]+dimsY[i]<= coordsY[j]+ lMax*(1 - b[i,j,2]);

# At most one horizontal relation should be implied.	
subject to oneOnlyX {i in N, j in 1..i-1}:
	b[i,j,1] + b[j,i,1] <= 1;

# At least one of the above constraint must be active (not relaxed) for all the coordinates i,j.
subject to overlapActivation {i in N, j in 1..i-1}:
	b[i,j,1] + b[i,j,2] + b[j,i,1] >= 1;

# First lower bound guaranteeing that all the circuits fit in the plate.
subject to lowerBoundl1:
	l * w >= sum {i in N} dimsX[i]*dimsY[i];

# Second lower bound guaranteeing that the highest circuit fits in the plate.
subject to lowerBoundl2:
	l >= max {i in N} dimsY[i];

# Upper bound for the length of the plate.
subject to upperBoundl:
	l <= lMax;