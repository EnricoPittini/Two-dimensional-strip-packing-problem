%000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000|
% PARAMETERS
1..infinity: w;
1..infinity: n;
array[1..n, 1..2] of 1..infinity: dims;
array[1..n] of 1..infinity: dimsX = col(dims,1);
array[1..n] of 1..infinity: dimsY = col(dims,2);
% TODO check efficiency

int: A_tot = sum(i in 1..n)(dimsX[i]*dimsY[i]);
int: h_max = max(dimsY);
int: l_min = max([h_max, A_tot div w]);
int: l_max = sum(dimsY);

% VARIABLES
var l_min..l_max: l;

%array[1..n, 1..2] of var int: coords;
array[1..n] of var 0..w: coordsX;
array[1..n] of var 0..infinity: coordsY;
% TODO possible double array to test

% CONSTRAINTS 
%constraint forall(i,j in 1..n where i<j)
%  ((coords[i,1]+dims[i,1]<=coords[j,1] \/ coords[j,1]+dims[j,1]<=coords[i,1]) \/
%  (coords[i,2]+dims[i,2]<=coords[j,2] \/ coords[j,2]+dims[j,2]<=coords[i,2]));
constraint forall(i,j in 1..n where i<j)
  ((coordsX[i]+dimsX[i]<=coordsX[j] \/ coordsX[j]+dimsX[j]<=coordsX[i]) \/
  (coordsY[i]+dimsY[i]<=coordsY[j] \/ coordsY[j]+dimsY[j]<=coordsY[i]));
constraint forall(i in 1..n) (coordsX[i]+dimsX[i]<=w);
constraint l = max(i in 1..n)(coordsY[i]+dimsY[i]);
solve minimize l;