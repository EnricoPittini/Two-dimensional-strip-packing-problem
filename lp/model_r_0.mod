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

####### DERIVED PARAMETERS
/** Upper bound for the length of the plate. */
param lMax := sum {i in N} dimsY[i];
/** MaxDims of the plate. */
var maxDims {N} integer >= 0;
subject to maxDimsValues {i in N}:
	maxDims[i] = max(dimsY[i], dimsX[i]);

####### VARIABLES
/** X coordinate of the bottom-left corner of the circuits. */
var coordsX {N} integer >=0 <=w;
/** Y coordinate of the bottom-left corner of the circuits. */
var coordsY {N} integer >=0 <=lMax;
/** Binary variables for each coordinate i,j related to the non-overlapping constraints. */
var b {N,N,1..2} integer >=0 <=1;
/** Binary variables regarding whether each circuit is rotated or not. */
var o {N} integer >=0 <=1;
/** Actual width of the eventually rotated circuits. */
var actualDimsX {N} integer >=0 <=w;
/** Actual height of the eventually rotated circuits. */
var actualDimsY {N} integer >=0 <=lMax;
/** The length of the plate. */
var l integer >= 0 <=lMax;

####### SOLVE
minimize result: l;

####### SUCH THAT:
# Constraints guaranteeing that all the circuits are within the bound of the plate.
subject to boundX {i in N}:
	coordsX[i]+actualDimsX[i]<= w;
subject to boundY {i in N}:
	coordsY[i]+actualDimsY[i]<= l;

# Constraints deciding the actual dimensions of the circuits according to their orientation in o
subject to orientedDimsX {i in N}:
	(1 - o[i]) * w[i] + o[i] * h[i] = actualDimsX[i];
subject to orientedDimsX {i in N}:
	(1 - o[i]) * h[i] + o[i] * w[i] = actualDimsY[i];

# No-overlapping constraints:
# If a constraint is active b[i,j,k] = 1 then the circuits must not overlap in the given dimension.
# Otherwise (the constraint is not active b[i,j,k] = 0), the constraint will always be satisfied thanks to the Big-M 
# technique and the overlapping in the given dimension will be ignored.	
subject to noOverlapX1 {i in N, j in 1..i-1}:
	coordsX[i]+actualDimsX[i]<= coordsX[j]+ w*(1 - b[i,j,1]);
subject to noOverlapX2 {i in N, j in 1..i-1}:
	coordsX[j]+actualDimsX[j]<= coordsX[i]+ w*(1 - b[j,i,1]);
subject to noOverlapY1 {i in N, j in 1..i-1}:
	coordsY[i]+actualDimsY[i]<= coordsY[j]+ lMax*(1 - b[i,j,2]);
subject to noOverlapY2 {i in N, j in 1..i-1}:
	coordsY[j]+actualDimsY[j]<= coordsY[i]+ lMax*(1 - b[j,i,2]);

# At most one vertical or horizontal relation should be implied.	
subject to oneOnlyX {i in N, j in 1..i-1}:
	b[i,j,1] + b[j,i,1] <= 1;
subject to oneOnlyY {i in N, j in 1..i-1}:
	b[i,j,2] + b[j,i,2] <= 1;

# At least one of the above constraint must be active (not relaxed) for all the coordinates i,j.
subject to overlapActivation {i in N, j in 1..i-1}:
	b[i,j,1] + b[i,j,2] + b[j,i,1] + b[j,i,2] >= 1;

# First lower bound guaranteeing that all the circuits fit in the plate.
subject to lowerBoundl1:
	l * w >= sum {i in N} dimsX[i]*dimsY[i];

# Second lower bound guaranteeing that the highest circuit fits in the plate.
subject to lowerBoundl2:
	l >= max {i in N} maxDims[i];

# Upper bound for the length of the plate.
subject to upperBoundl:
	l <= lMax;