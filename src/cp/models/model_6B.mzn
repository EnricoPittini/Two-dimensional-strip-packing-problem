%---------------------------------------------------------------------------------------------------------------------------%
%                                                         MODEL 6B                                                          %
%                                                                                                                           %
% Model that uses solver Chuffed and the following search heuristic:                                                                           %
% - Always select the lowest possible value in the domain of the length of the plate `l`.                                   %
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
/** The minimum height of a circuit */
int: h_min = min(dimsY);
/** The maximum height of a circuit */
int: h_max = max(dimsY);
/** The minimum width of a circuit */
int: w_min = min(dimsX);
/** The maximum width of a circuit */
int: w_max = max(dimsX);
/** The lower bound for the length */
int: l_min = max([h_max, A_tot div w]);
/** Minimum number of circuits per row */
int: min_rects_per_row = w div w_max;
/** The upper bound for the length */
int: l_max = if min_rects_per_row = 1 
  then sum(dimsY) 
  else let{array [1..n] of int: sorted_dimsY = reverse(sort(dimsY))} in 
    sum([sorted_dimsY[k] | k in 1..n where k mod min_rects_per_row = 1]) 
endif;

%%%%%%% VARIABLES
/** The length of the plate */
var l_min..l_max: l;
/** Y coordinate of the left-bottom corner of the circuits */
array[1..n] of var 0..l_max-h_min: coordsY;
/** X coordinate of the left-bottom corner of the circuits */
array[1..n] of var 0..w-w_min: coordsX;


%%%%%%% CONSTRAINTS 
% The circuits, given by their left-bottom corners `coordsX,coordsY` and sizes `dimsX,dimsY`, must be non-overlapping
constraint diffn(coordsX, coordsY, dimsX, dimsY);

% Cumulative implied constraint in which:
%    - the starting times of the tasks are coordsX
%    - the durations of the tasks are dimsX
%    - the resource recquirements of the tasks are dimsY
%    - the maximum resource bound is l
constraint cumulative(coordsX, dimsX, dimsY, l);

% Each circuit must not exceed the width of the plate
constraint forall(i in 1..n) (coordsX[i]+dimsX[i]<=w);
% The length of the plate is the maximum height reached
constraint l = max(i in 1..n)(coordsY[i]+dimsY[i]);


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

solve :: search_ann_l_from_min minimize l;
