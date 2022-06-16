%---------------------------------------------------------------------------------------------------------------------------%
%                                                         MODEL 0                                                           %
%                                                                                                                           %
%---------------------------------------------------------------------------------------------------------------------------%

include "cumulative.mzn";
include "diffn.mzn";


%%%%%%% PARAMETERS
/** The width of the plate. */
int: w;
/** The number of the circuits. */
int: n;
/** Dims X (i.e. width) and Y (i.e. height) of the circuits. */
array[1..n, 1..2] of int: dims;

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

%%%%%%% VARIABLES
% The length of the plate
var l_min..l_max: l;

array[1..n] of var 0..l_max-h_min: coordsY;  % Coords X of the left-bottom corner of the rectangles
array[1..n] of var 0..w-w_min: coordsX;  % Coords Y of the left-bottom corner of the rectangles

%%%%%%% SOLVING
solve minimize l;

%%%%%%% SUCH THAT
% Non overlapping (http://yetanothermathprogrammingconsultant.blogspot.com/2017/07/rectangles-no-overlap-constraints.html)
% This link provides symmetry breaking information (https://stackoverflow.com/questions/47406225/linearprogramming-non-overlapping-constraint)

/** Big-M trick */
%int: M = round(infinity);
int: M = 1000000;

/** Binary variables for each coordinate i,j related to the non-overlapping constraints. */
array[1..n, 1..n, 1..4] of var 0..1: b;

% If a constraint is active b[i,j,k] = 0 then the circuits must not overlap in the given dimension.
% Otherwise (the constraint is not active b[i,j,k] = 1). In practice the constraint will always be satisfied thanks to
% the Big-M trick and the overlapping in the given dimension will be ignored.
constraint forall(i,j in 1..n where i<j)(coordsX[i] + dimsX[i] <= coordsX[j] + M*b[i,j,1]);
constraint forall(i,j in 1..n where i<j)(coordsY[i] + dimsY[i] <= coordsY[j] + M*b[i,j,2]);
constraint forall(i,j in 1..n where i<j)(coordsX[j] + dimsX[j] <= coordsX[i] + M*b[i,j,3]);
constraint forall(i,j in 1..n where i<j)(coordsY[j] + dimsY[j] <= coordsY[i] + M*b[i,j,4]);
% At least one of the above constraint must be active (not relaxed) for all the coordinates i,j.
constraint forall(i,j in 1..n where i<j)(sum(b[i,j,..]) <= 3);

% In bound
constraint forall(i in 1..n)(coordsX[i] + dimsX[i] <= w);
constraint forall(i in 1..n)(coordsY[i] + dimsY[i] <= l);
