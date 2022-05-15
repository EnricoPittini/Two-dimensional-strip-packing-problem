%000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000|
% PARAMETERS
include "cumulative.mzn";
include "diffn.mzn";
%include "gecode.mzn";

1..infinity: w;
1..infinity: n;
array[1..n, 1..2] of int: dims;
array[1..n] of int: dimsX = col(dims,1);
array[1..n] of int: dimsY = col(dims,2);
% TODO check efficiency

array [1..n] of int: areas = [dimsX[i]*dimsY[i] | i in 1..n];
int: A_tot = sum(areas);
int: h_max = max(dimsY);
int: l_min = max([h_max, A_tot div w]);
int: l_max = sum(dimsY);

% VARIABLES
var l_min..l_max: l;

%array[1..n, 1..2] of var int: coords;
array[1..n] of var 0..l_max: coordsY;
array[1..n] of var 0..w: coordsX;
% TODO possible double array to test

% CONSTRAINTS 
%constraint forall(i,j in 1..n where i<j)
%  ((coords[i,1]+dims[i,1]<=coords[j,1] \/ coords[j,1]+dims[j,1]<=coords[i,1]) \/
%  (coords[i,2]+dims[i,2]<=coords[j,2] \/ coords[j,2]+dims[j,2]<=coords[i,2]));
constraint cumulative(coordsX, dimsX, dimsY, l);
constraint cumulative(coordsY, dimsY, dimsX, w);


constraint diffn(coordsX,
                coordsY,
                dimsX,
                dimsY);



%constraint forall(i,j in 1..n where i<j)
%  ((coordsX[i]+dimsX[i]<=coordsX[j] \/ coordsX[j]+dimsX[j]<=coordsX[i]) \/
%  (coordsY[i]+dimsY[i]<=coordsY[j] \/ coordsY[j]+dimsY[j]<=coordsY[i]));
constraint forall(i in 1..n) (coordsX[i]+dimsX[i]<=w);
%constraint forall(i in 1..n) (coordsY[i]+dimsY[i]<=l);
constraint l = max(i in 1..n)(coordsY[i]+dimsY[i]);

% SOLVING
%array[1..n] of int: indices = reverse(arg_sort(areas));
%array[1..2*n] of var int: variables = [if (i mod 2 = 0) then coordsY[indices[i div 2]] else coordsX[indices[(i+1) div 2]] endif
%  | i in 1..2*n];
array[1..n] of var int:sorted_coordsX = reverse(sort_by(coordsX, dimsX));
array[1..n] of var int:sorted_coordsY = reverse(sort_by(coordsY, dimsX));
array[1..2*n] of var int: variables = [if (i mod 2 = 0) then sorted_coordsY[i div 2] else sorted_coordsX[(i+1) div 2] endif
  | i in 1..2*n];
ann: search_ann = int_search(variables, input_order, indomain_min);
%ann: search_annY = int_search(reverse(sort_by(coordsY, dimsY)), input_order, indomain_min);
%ann: search_annX = int_search(reverse(sort_by(coordsX, dimsX)), input_order, indomain_min);

%solve :: seq_search([search_annY, search_annX]) 
solve :: search_ann
%  :: restart_luby(250)
%  ::relax_and_reconstruct(coordsY, 85)
minimize l;