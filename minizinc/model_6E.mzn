%000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000|

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
int: h_min = min(dimsY);  % The minimum height of a rectangle
int: h_max = max(dimsY);  % The maximum height of a rectangle
int: w_min = min(dimsX);  % The minimum width of a rectangle
int: w_max = max(dimsX);  % The maximum width of a rectangle
int: l_min = max([h_max, A_tot div w]);  % The lower bound for the length
int: max_rects_per_row = w div w_max; % Maximum number of rectangles per row
int: max_rects_per_col = ceil(n / max_rects_per_row); % Maximum number of rectangles per column
int: l_max = sum(sort(dimsY)[n-max_rects_per_col+1..n]);  % The upper bound for the length


%%%%%%% VARIABLES
% The length of the plate
var l_min..l_max: l;

array[1..n] of var 0..l_max-h_min: coordsY;  % Coords X of the left-bottom corner of the rectangles
array[1..n] of var 0..w-w_min: coordsX;  % Coords Y of the left-bottom corner of the rectangles


%%%%%%% CONSTRAINTS 
% The rectangles, given by their left-bottom corners `coordsX,coordsY` and sizes `dimsX,dimsY`, must be non-overlapping
constraint diffn(coordsX, coordsY, dimsX, dimsY);

% Cumulative constraint in which:
%    - the starting times of the tasks are coordsX
%    - the durations of the tasks are dimsX
%    - the resource recquirements of the tasks are dimsY
%    - the maximum resource bound is l
constraint cumulative(coordsX, dimsX, dimsY, l);
% Cumulative constraint in which:
%    - the starting times of the tasks are coordsY
%    - the durations of the tasks are dimsY
%    - the resource recquirements of the tasks are dimsX
%    - the maximum resource bound is w
% constraint cumulative(coordsY, dimsY, dimsX, w);

% Each rectangle must not exceed the width of the plate (IT IS AN IMPLIED CONSTRAINT)
constraint forall(i in 1..n) (coordsX[i]+dimsX[i]<=w);
%constraint forall(i in 1..n) (coordsY[i]+dimsY[i]<=l);
% The length of the plate is the maximum height reached (IT IS AN IMPLIED CONSTRAINT)
constraint l = max(i in 1..n)(coordsY[i]+dimsY[i]);


%%%%%%% SYMMETRY BREAKING
constraint let{int: w_half = ceil(w/2);} in (sum([areas[i] | i in 1..n where coordsX[i] >= ceil(w/2)]) <= A_tot / 2);

%%%%%%% SOLVING

% Variables selection heuristic: it is based on the rectangles widths; it interleaves coordX and coordY.
% Variables order: coordX of the rectangle with max width; coordY of the rectangle with max width; coordX of the rectangle 
% with second max width; coordY of the rectangle with second max width; ... .
%array[1..n] of var int: sorted_coordsX = reverse(sort_by(coordsX, dimsX));
%array[1..n] of var int: sorted_coordsY = reverse(sort_by(coordsY, dimsX));
%array[1..2*n] of var int: variables = [if (i mod 2 = 0) then sorted_coordsY[i div 2] else sorted_coordsX[(i+1) div 2] endif
%  | i in 1..2*n];
%ann: search_ann = int_search(variables, input_order, indomain_min);

%solve :: search_ann
%minimize l;

solve minimize l;