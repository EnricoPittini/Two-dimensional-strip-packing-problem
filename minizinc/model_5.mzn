%---------------------------------------------------------------------------------------------------------------------------%
%                                                          MODEL 7                                                          %
% Dual model.                                                                                                               %
%---------------------------------------------------------------------------------------------------------------------------%

include "cumulative.mzn";
include "diffn.mzn";
include "globals.mzn";


%%%%%%% PARAMETERS
int: w;  % The width of the plate
int: n;  % Number of the rectangles
array[1..n, 1..2] of int: dims;  % Dims X (i.e. width) and Y (i.e. height) of the rectangles
array[1..n] of int: dimsX = col(dims,1);
array[1..n] of int: dimsY = col(dims,2);

array [1..n] of int: areas = [dimsX[i]*dimsY[i] | i in 1..n];  % The areas of the rectangles
int: A_tot = sum(areas);  % The overall area of all the given rectangles
int: h_min = min(dimsY);  % The minimum height of a rectangle
int: h_max = max(dimsY);  % The maximum height of a rectangle
int: w_min = min(dimsX);  % The minimum width of a rectangle
int: w_max = max(dimsX);  % The maximum width of a rectangle
int: l_min = max([h_max, A_tot div w]);  % The lower bound for the length
int: min_rects_per_row = w div w_max; % Minimum number of rectangles per row
int: max_rects_per_col = ceil(n / max([1, min_rects_per_row])); % Maximum number of rectangles per column
% The upper bound for the length
int: l_max = if min_rects_per_row = 1 
  then sum(dimsY) 
  else let{array [1..n] of int: sorted_dimsY = reverse(sort(dimsY))} in 
    sum([sorted_dimsY[k] | k in 1..n where k mod min_rects_per_row = 1]) 
endif;

%%%%%%% VARIABLES MODEL 1
% The length of the plate
var l_min..l_max: l;

array[1..n] of var 0..l_max-h_min: coordsY;  % Coords X of the left-bottom corner of the rectangles
array[1..n] of var 0..w-w_min: coordsX;  % Coords Y of the left-bottom corner of the rectangles

%%%%%%% VARIABLES MODEL 2
array[0..l_max-1, 0..w-1] of var 0..n: grid;  % Grid representation of the plate where each cell belongs to one rectangle

%%%%%%% CONSTRAINTS MODEL 1 
% The rectangles, given by their left-bottom corners `coordsX,coordsY` and sizes `dimsX,dimsY`, must be non-overlapping
constraint diffn(coordsX, coordsY, dimsX, dimsY);

% Cumulative constraint in which:
%    - the starting times of the tasks are coordsX
%    - the durations of the tasks are dimsX
%    - the resource recquirements of the tasks are dimsY
%    - the maximum resource bound is l
constraint cumulative(coordsX, dimsX, dimsY, l);

% Each rectangle must not exceed the width of the plate (IT IS AN IMPLIED CONSTRAINT)
constraint forall(i in 1..n) (coordsX[i]+dimsX[i]<=w);
% The length of the plate is the maximum height reached (IT IS AN IMPLIED CONSTRAINT)
constraint l = max(i in 1..n)(coordsY[i]+dimsY[i]);

%%%%%%% CONSTRAINTS MODEL 2
% In each row each rectangle either completely fits in or is not in the row
constraint forall(i in 0..l_max-1, j in 1..n)(member([0, dimsX[j]], count(row(grid,i), j)));
% constraint forall(i in 1..l, j in 1..n)(count_eq(row(grid,i), j, 0) \/ count_eq(row(grid,i), j, dimsX[j]));
% In each column each rectangle either completely fits in or is not in the column
constraint forall(i in 0..w-1, j in 1..n)(member([0, dimsY[j]], count(col(grid,i), j)));
% constraint forall(i in 1..w, j in 1..n)(count_eq(col(grid,i), j, 0) \/ count_eq(col(grid,i), j, dimsY[j]));

%global_cardinality_low_up_closed(row(grid,i), 1..n,
%                                           0,
%                                           0))

%%%%%%% CHANNELING CONSTRAINTS
%constraint forall(i in 1..l_max, j in 1..w, k in 1..n)
%  (grid[i,j] = k <-> ((coordsX[k] <= i /\ i <= coordsX[k] + dimsX[k]) /\ (coordsY[k] <= j /\ j <= coordsY[k] + dimsY[k])));
constraint forall(i in 0..l_max-1, j in 0..w-1, k in 1..n)
  (grid[i,j] = k <-> (coordsX[k] <= j /\ j < coordsX[k] + dimsX[k] /\ coordsY[k] <= i /\ i < coordsY[k] + dimsY[k]));


%%%%%%% SYMMETRY BREAKING
% Symmetry breaking constraint that imposes that the area of the rectangles on the right half of the plate should be less
% or equal than half of the total area of the rectangles.
constraint let{int: w_half = ceil(w/2)} in (sum([areas[i] | i in 1..n where coordsX[i] >= w_half]) <= A_tot / 2);

% Symmetry breaking constraint that imposes that the area of the rectangles on the top half of the plate should be less
% or equal than half of the total area of the rectangles.
constraint sum([areas[i] | i in 1..n where coordsY[i] > l div 2]) <= A_tot / 2;

%%%%%%% SOLVING
solve minimize l;
