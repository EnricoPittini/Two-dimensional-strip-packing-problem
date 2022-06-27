param n integer > 0;
set N := 1..n;
param w integer > 0;
param dimsX {N} integer >0 <=w;
param dimsY {N} integer >0;
param lMax = sum {i in N} dimsY[i];

var boundX {N} integer >= 0 <=w;
var boundY {N} integer >= 0 <=lMax;
var noOverlapX {N,N} integer >= 0 <=100;
var noOverlapY {N,N} integer >= 0 <=100;
var oneOnly {N,N} integer >= 0 <=100;
var overlapActivation {N,N} integer >= 0 <=100;
var lowerBoundl1 integer >= 0 <=100;
var lowerBoundl2 integer >= 0 <=100;
var upperBoundl integer >= 0 <=100;

maximize result: sum {i in N} ((w - dimsX[i])*boundX[i] - dimsY[i]*boundY[i]) + 
	sum {i in N, j in 1..i-1} ( (w - dimsX[i])*noOverlapX[i,j] + (w - dimsX[j])*noOverlapX[j,i] +
	(lMax - dimsY[i])*noOverlapY[i,j] + (lMax - dimsY[j])*noOverlapY[j,i] + oneOnly[i,j] + 
	oneOnly[j,i] - overlapActivation[i,j] ) - (sum {i in N} dimsX[i]*dimsY[i])*lowerBoundl1 -
	(max {i in N} dimsY[i])*lowerBoundl2 + lMax*upperBoundl;

#CHECK SIGN

subject to coordsX {i in N}:
	boundX[i] + sum {j in 1..i-1} (noOverlapX[j,i] - noOverlapX[i,j] ) + sum {j in i+1..n}(noOverlapX[i,j]-noOverlapX[j,i]) <= 0;
subject to coordsY {i in N}:
	boundY[i] + sum {j in 1..i-1} (noOverlapY[j,i] - noOverlapY[i,j] ) + sum {j in i+1..n}(noOverlapY[i,j]-noOverlapY[j,i]) <= 0;
subject to b1 {i in N, j in N}:
	w*(noOverlapX[i,j]+noOverlapX[j,i]) + oneOnly[i,j] + oneOnly[j,i] - overlapActivation[i,j] - overlapActivation[j,i] <= 0;
subject to b2 {i in N, j in N}:
	lMax*(noOverlapY[i,j]+noOverlapY[j,i]) + oneOnly[i,j] + oneOnly[j,i] - overlapActivation[i,j] - overlapActivation[j,i] <= 0;
subject to l:
	(- sum {i in N} boundY[i]) + - w*lowerBoundl1 - lowerBoundl2 + upperBoundl <= 1;
	