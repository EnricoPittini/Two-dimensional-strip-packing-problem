%---------------------------------------------------------------------------------------------------------------------------%
%                                                        MODEL R 1A                                                         %
% New model with updated bounds and all cumulative constraints.                                                             %
%---------------------------------------------------------------------------------------------------------------------------%

include "cumulative.mzn";
include "diffn.mzn";


%%%%%%% PARAMETERS
/** The width of the plate */
int: w;
/** Number of circuits */
int: n;
/** Matrix containing for each circuit its dimensions (width and height) */
array[1..n, 1..2] of int: dims;
/** Derived width of the circuits */
array[1..n] of int: dimsX = col(dims,1);
/** Derived height of the circuits */
array[1..n] of int: dimsY = col(dims,2);

/** The areas of the circuits */
array [1..n] of int: areas = [dimsX[i]*dimsY[i] | i in 1..n];
/** The overall area of all the given circuits */
int: A_tot = sum(areas);
/** The lower bound for the length */
int: l_min = A_tot div w;
/** Length of the maximum dimension among all circuits */
int: maxDim = max(dimsX ++ dimsY);
/** Length of the minimum dimension among all circuits */
int: minDim = min(dimsX ++ dimsY);
/** Minimum number of circuits per row */
int: min_rects_per_row = w div maxDim;
/** The upper bound for the length */
int: l_max = if min_rects_per_row < 2 
  then sum([max([dimsX[i], dimsY[i]]) | i in 1..n])
  else let{array [1..n] of int: sorted_dims = reverse(sort([max([dimsX[i], dimsY[i]]) | i in 1..n ]))} in 
    sum([sorted_dims[k] | k in 1..n where k mod min_rects_per_row = 1]) 
endif;


%%%%%%% VARIABLES
/** The length of the plate */
var l_min..l_max: l;
/** Y coordinate of the left-bottom corner of the circuits */
array[1..n] of var 0..l_max-minDim: coordsY;
/** X coordinate of the left-bottom corner of the circuits */
array[1..n] of var 0..w-minDim: coordsX;
/** Array expressing whether each circuit is rotated or not */
array[1..n] of var bool: rotations;
/** Actual width of the circuits according to their rotation */
array[1..n] of var 1..maxDim: actualDimsX;
actualDimsX = [if rotations[i] then dimsY[i] else dimsX[i] endif | i in 1..n];
/** Actual height of the circuits according to their rotation */
array[1..n] of var 1..maxDim: actualDimsY; 
actualDimsY = [if rotations[i] then dimsX[i] else dimsY[i] endif | i in 1..n];


%%%%%%% CONSTRAINTS 
% The circuits, given by their left-bottom corners `coordsX,coordsY` and sizes `actualDimsX,actualDimsY`, must be 
% non-overlapping
constraint diffn(coordsX, coordsY, actualDimsX, actualDimsY);

% Cumulative implied constraint in which:
%    - the starting times of the tasks are coordsX
%    - the durations of the tasks are actualDimsX
%    - the resource recquirements of the tasks are actualDimsY
%    - the maximum resource bound is l
constraint cumulative(coordsX, actualDimsX, actualDimsY, l);

% Cumulative implied constraint in which:
%    - the starting times of the tasks are coordsX
%    - the durations of the tasks are actualDimsY
%    - the resource recquirements of the tasks are actualDimsX
%    - the maximum resource bound is w
constraint cumulative(coordsY, actualDimsY, actualDimsX, w);

% Each circuit must not exceed the width of the plate
constraint forall(i in 1..n) (coordsX[i]+actualDimsX[i]<=w);
% The length of the plate is the maximum height reached
constraint l = max(i in 1..n)(coordsY[i]+actualDimsY[i]);


%%%%%%% SYMMETRY BREAKING
% Symmetry breaking constraint that imposes that the area of the circuits on the right half of the plate should be less
% or equal than half of the total area of the circuits.
constraint let{int: w_half = ceil(w/2)} in (sum([areas[i] | i in 1..n where coordsX[i] >= w_half]) <= A_tot / 2);
% Symmetry breaking constraint that imposes that the area of the circuits on the top half of the plate should be less
% or equal than half of the total area of the circuits.
constraint sum([areas[i] | i in 1..n where coordsY[i] > l div 2]) <= A_tot / 2;


%%%%%%% SOLVING
solve minimize l;
