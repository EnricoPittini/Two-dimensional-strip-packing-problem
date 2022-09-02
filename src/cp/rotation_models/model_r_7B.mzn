%---------------------------------------------------------------------------------------------------------------------------%
%                                                         MODEL R 7B ☑                                                     %
% Model that extends `MODEL R 2B` and adds and the following search heuristic:                                              %
% - Determine the rotation of the circuits by decreasing order with respect to their areas;                                 %
% - Apply an ordered search on the interleaved `coordsX` and `coordsY` of the circuits sorted by decreasing order with      %
%   respect to the value of their maximum dimension. Always choose the lowest value of the domains first.                   %
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
/** Length of the maximum dimension of each circuit */
array [1..n] of int: maxDims = [max([dimsX[i], dimsY[i]]) | i in 1..n];
/** Length of the maximum dimension among all circuits */
int: maxDim = max(maxDims);
/** Length of the minimum dimension among all circuits */
int: minDim = min(dimsX ++ dimsY);
/** Minimum number of circuits per row */
int: min_rects_per_row = w div maxDim;
/** The upper bound for the length */
int: l_max = if min_rects_per_row < 2 
  then sum(maxDims)
  else let{array [1..n] of int: sorted_dims = reverse(sort(maxDims))} in 
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
/** Actual height of the circuits according to their rotation */
array[1..n] of var 1..maxDim: actualDimsY;


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

% Each circuit must not exceed the width of the plate
constraint forall(i in 1..n) (coordsX[i]+actualDimsX[i]<=w);
% The length of the plate is the maximum height reached
constraint l = max(i in 1..n)(coordsY[i]+actualDimsY[i]);

% Constraints imposing that `actualDimsX` and `actualDimsY` must have values either `dimsX` or `dimsY`
constraint forall(i in 1..n)(actualDimsX[i] = dimsX[i] \/ actualDimsX[i] = dimsY[i]); 
constraint forall(i in 1..n)(actualDimsY[i] = dimsX[i] \/ actualDimsY[i] = dimsY[i]);

% Constraints assignin the `actualDimsX` and `actualDimsY` based on the rotation of the circuit
constraint forall(i in 1..n)(rotations[i] = false <-> (actualDimsX[i] = dimsX[i] /\ actualDimsY[i] = dimsY[i]));
constraint forall(i in 1..n)(rotations[i] = true -> (actualDimsX[i] = dimsY[i] /\ actualDimsY[i] = dimsX[i]));


%%%%%%% SYMMETRY BREAKING
% Symmetry breaking constraint that imposes that the area of the circuits on the right half of the plate should be less
% or equal than half of the total area of the circuits.
constraint let{int: w_half = ceil(w/2)} in (sum([areas[i] | i in 1..n where coordsX[i] >= w_half]) <= A_tot / 2);
% Symmetry breaking constraint that imposes that the area of the circuits on the top half of the plate should be less
% or equal than half of the total area of the circuits.
constraint sum([areas[i] | i in 1..n where coordsY[i] > l div 2]) <= A_tot / 2;


%%%%%%% SOLVING
/** Search annotation imposing that, regarding variable l, the lowest possible value in the domain is chosen first */
ann: search_ann_l_from_min = int_search([l], input_order, indomain_min, complete);

/** Variables of `coordsX` sorted by the maximum dimension of the circuits in a decreasing order */
array[1..n] of var int: sorted_coordsX = reverse(sort_by(coordsX, maxDims));
/** Variables of `coordsY` sorted by the maximum dimension of the circuits in a decreasing order */
array[1..n] of var int: sorted_coordsY = reverse(sort_by(coordsY, maxDims));
/** Array containing the coordinates of the circuits (`coordsX`, `coordsY`) sorted by their maximum dimension in a 
decreasing order. Variables order: x coordinate of the circuit with max dimension; y coordinate of the circuit with max 
dimension; x coordinate of the circuit with second max dimension; y coordinate of the circuit with second max 
dimension; ... . */
array[1..2*n] of var int: variables = [if (i mod 2 = 0) then sorted_coordsY[i div 2] else sorted_coordsX[(i+1) div 2] endif
  | i in 1..2*n];
/** Search annotation imposing to apply an ordered search through the variables expressed in `variables` selecting the 
minimum value of their domains first */
ann: search_ann_dec_maxDims = int_search(variables, input_order, indomain_min);

/** Search annotation imposing to select the rotation of the circuit with greater area first. */
ann: search_ann_rotations = bool_search(reverse(sort_by(rotations, areas)), input_order, indomain_min);

solve :: seq_search([search_ann_l_from_min, search_ann_rotations, search_ann_dec_maxDims]) minimize l;
