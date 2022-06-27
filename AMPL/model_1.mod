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

minimize result: l;

subject to boundX {i in N}:
	coordsX[i]+dimsX[i]<= w;
subject to boundY {i in N}:
	coordsY[i]+dimsY[i]<= l;
	
subject to noOverlapX1 {i in N, j in 1..i-1}:
	coordsX[i]+dimsX[i]<= coordsX[j]+ w*(1 - b[i,j,1]);
subject to noOverlapX2 {i in N, j in 1..i-1}:
	coordsX[j]+dimsX[j]<= coordsX[i]+ w*(1 - b[j,i,1]);
subject to noOverlapY1 {i in N, j in 1..i-1}:
	coordsY[i]+dimsY[i]<= coordsY[j]+ lMax*(1 - b[i,j,2]);
subject to noOverlapY2 {i in N, j in 1..i-1}:
	coordsY[j]+dimsY[j]<= coordsY[i]+ lMax*(1 - b[j,i,2]);
	
subject to oneOnlyX {i in N, j in 1..i-1}:
	b[i,j,1] + b[j,i,1] <= 1;
subject to oneOnlyY {i in N, j in 1..i-1}:
	b[i,j,2] + b[j,i,2] <= 1;
subject to overlapActivation {i in N, j in 1..i-1}:
	b[i,j,1] + b[i,j,2] + b[j,i,1] + b[j,i,2] >= 1;
	
subject to lowerBoundl1:
	l * w >= sum {i in N} dimsX[i]*dimsY[i];
subject to lowerBoundl2:
	l >= max {i in N} dimsY[i];
subject to upperBoundl:
	l <= lMax;