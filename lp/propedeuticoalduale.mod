param n integer > 0;
set N := 1..n;
param w integer > 0;
param dimsX {N} integer >0 <=w;
param dimsY {N} integer >0;
param lMax = sum {i in N} dimsY[i];

var coordsX {N} integer >=0 <=w;
var coordsY {N} integer >=0;
var b {N,N,1..2} integer >=0 <=1;
var l integer >= 0;
#SLACK VARIABLES
var slackBoundX {N} integer >=0;
var slackBoundY {N} integer >=0;
var slackNoOverlap {N,N,1..2} integer >=0;
var slackOnlyOne {N,N} integer >=0;
var slackOverlapActivation {N,N} integer >=0;
var slackLowerBoundl1 integer >=0;
var slackLowerBoundl2 integer >=0;
var slackUpperBoundl integer >=0;


minimize result: l;

subject to boundX {i in N}:
	coordsX[i] + slackBoundX[i] = w - dimsX[i];
subject to boundY {i in N}:
	coordsY[i] - l + slackBoundY[i] = - dimsY[i] ;
	
subject to noOverlapX1 {i in N, j in 1..i-1}:
	coordsX[i] + slackNoOverlap[i,j,1] - coordsX[j] + w*b[i,j,1] = w - dimsX[i];
subject to noOverlapX2 {i in N, j in 1..i-1}:
	coordsX[j] + slackNoOverlap[j,i,1] - coordsX[i] + w*b[j,i,1] = w - dimsX[j];
subject to noOverlapY1 {i in N, j in 1..i-1}:
	coordsY[i] + slackNoOverlap[i,j,2] - coordsY[j] + lMax*b[i,j,2] = lMax - dimsY[i];
subject to noOverlapY2 {i in N, j in 1..i-1}:
	coordsY[j] + slackNoOverlap[j,i,2] - coordsY[i] + lMax*b[j,i,2] = lMax - dimsY[j];
	
subject to oneOnlyX {i in N, j in 1..i-1}:
	b[i,j,1] + b[j,i,1] + slackOnlyOne[i,j] = 1;
subject to oneOnlyY {i in N, j in 1..i-1}:
	b[i,j,2] + b[j,i,2] + slackOnlyOne[j,i] = 1;
subject to overlapActivation {i in N, j in 1..i-1}:
	-(b[i,j,1] + b[i,j,2] + b[j,i,1] + b[j,i,2]) + slackOverlapActivation[i,j] = -1;
	
subject to lowerBoundl1:
	-l * w + slackLowerBoundl1 = -sum {i in N} dimsX[i]*dimsY[i];
subject to lowerBoundl2:
	-l + slackLowerBoundl2 = -max {i in N} dimsY[i];
subject to upperBoundl:
	l + slackUpperBoundl = lMax;