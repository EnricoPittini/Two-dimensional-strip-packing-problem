%---------------------------------------------------------------------------------------------------------------------------%
%                                                         MODEL R 3B                                                        %
% New model adding the following constraints:                                                                               %
% - If circuits do not fit one on top of the other they must stay side by side;                                             %
% - If circuits do not fit one on the side of the other they must stay one on top of the other.                             %
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

% Circuits which can't stay one of the side of the other are up or down
constraint forall(i,j in 1..n where i < j)
  (actualDimsX[i] + actualDimsX[j] > w -> ((coordsY[i] < coordsY[j] -> coordsY[i] + actualDimsY[i] <= coordsY[j]) /\ 
  (coordsY[j] < coordsY[i] -> coordsY[j] + actualDimsY[j] <= coordsY[i])));
  
% Circuits which can't stay one on top of the other are one to the side of the other
constraint forall(i,j in 1..n where i < j)
  (actualDimsY[i] + actualDimsY[j] > l -> ((coordsX[i] < coordsX[j] -> coordsX[i] + actualDimsX[i] <= coordsX[j]) /\
  (coordsX[j] < coordsX[i] -> coordsX[j] + actualDimsX[j] <= coordsX[i])));


%%%%%%% SYMMETRY BREAKING
% Symmetry breaking constraint that imposes that the area of the circuits on the right half of the plate should be less
% or equal than half of the total area of the circuits.
constraint let{int: w_half = ceil(w/2)} in (sum([areas[i] | i in 1..n where coordsX[i] >= w_half]) <= A_tot / 2);
% Symmetry breaking constraint that imposes that the area of the circuits on the top half of the plate should be less
% or equal than half of the total area of the circuits.
constraint sum([areas[i] | i in 1..n where coordsY[i] > l div 2]) <= A_tot / 2;


%%%%%%% SOLVING
solve minimize l;
