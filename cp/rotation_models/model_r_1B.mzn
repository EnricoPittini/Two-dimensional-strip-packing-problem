%---------------------------------------------------------------------------------------------------------------------------%
%                                                        MODEL R 1B ☑                                                      %
% New model with updated bounds and the cumulative constraint regarding just the length;                                    %
%---------------------------------------------------------------------------------------------------------------------------%

include "cumulative.mzn";
include "diffn.mzn";


%%%%%%% PARAMETERS
int: w;  % The width of the plate
int: n;  % Number of the rectangles
array[1..n, 1..2] of int: dims;  % Dims X (i.e. width) and Y (i.e. height) of the rectangles
array[1..n] of int: dimsX = col(dims,1);
array[1..n] of int: dimsY = col(dims,2);

array [1..n] of int: areas = [dimsX[i]*dimsY[i] | i in 1..n];  % The areas of the rectangles
int: A_tot = sum(areas);  % The overall area of all the given rectangles

int: l_min = A_tot div w; % The lower bound for the length

int: maxDim = max(dimsX ++ dimsY);
int: minDim = min(dimsX ++ dimsY);

int: min_rects_per_row = w div maxDim; % Minimum number of rectangles per row
int: max_rects_per_col = ceil(n / max([1, min_rects_per_row])); % Maximum number of rectangles per column
% The upper bound for the length.
int: l_max = if min_rects_per_row < 2 
  then sum([max([dimsX[i], dimsY[i]]) | i in 1..n])
  else let{array [1..n] of int: sorted_dims = reverse(sort([max([dimsX[i], dimsY[i]]) | i in 1..n ]))} in 
    sum([sorted_dims[k] | k in 1..n where k mod min_rects_per_row = 1]) 
endif;



%%%%%%% VARIABLES
% The length of the plate
var l_min..l_max: l;

array[1..n] of var 0..l_max-minDim: coordsY;  % Coords X of the left-bottom corner of the rectangles
array[1..n] of var 0..w-minDim: coordsX;  % Coords Y of the left-bottom corner of the rectangles

array[1..n] of var bool: rotations;

array[1..n] of var 1..maxDim: actualDimsX;
actualDimsX = [if rotations[i] then dimsY[i] else dimsX[i] endif | i in 1..n];

array[1..n] of var 1..maxDim: actualDimsY; 
actualDimsY = [if rotations[i] then dimsX[i] else dimsY[i] endif | i in 1..n];

%%%%%%% CONSTRAINTS 
% The rectangles, given by their left-bottom corners `coordsX,coordsY` and sizes `dimsX,dimsY`, must be non-overlapping
constraint diffn(coordsX, coordsY, actualDimsX, actualDimsY);

% Cumulative constraint in which:
%    - the starting times of the tasks are coordsX
%    - the durations of the tasks are dimsX
%    - the resource recquirements of the tasks are dimsY
%    - the maximum resource bound is l
constraint cumulative(coordsX, actualDimsX, actualDimsY, l);

% Each rectangle must not exceed the width of the plate (IT IS AN IMPLIED CONSTRAINT)
constraint forall(i in 1..n) (coordsX[i]+actualDimsX[i]<=w);
% The length of the plate is the maximum height reached (IT IS AN IMPLIED CONSTRAINT)
constraint l = max(i in 1..n)(coordsY[i]+actualDimsY[i]);


%%%%%%% SYMMETRY BREAKING
% Symmetry breaking constraint that imposes that the area of the rectangles on the right half of the plate should be less
% or equal than half of the total area of the rectangles.
constraint let{int: w_half = ceil(w/2)} in (sum([areas[i] | i in 1..n where coordsX[i] >= w_half]) <= A_tot / 2);

% Symmetry breaking constraint that imposes that the area of the rectangles on the top half of the plate should be less
% or equal than half of the total area of the rectangles.
constraint sum([areas[i] | i in 1..n where coordsY[i] > l div 2]) <= A_tot / 2;



%%%%%%% SOLVING
solve minimize l;
