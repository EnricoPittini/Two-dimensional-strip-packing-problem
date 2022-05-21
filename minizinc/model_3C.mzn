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
int: h_max = max(dimsY);  % The maximum height of a rectangle
int: l_min = max([h_max, A_tot div w]);  % The lower bound for the length
int: l_max = sum(dimsY);  % The upper bound for the length


%%%%%%% VARIABLES
% The length of the plate
var l_min..l_max: l;

array[1..n] of var 0..l_max: coordsY;  % Coords X of the left-bottom corner of the rectangles
array[1..n] of var 0..w: coordsX;  % Coords Y of the left-bottom corner of the rectangles


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
constraint cumulative(coordsY, dimsY, dimsX, w);

% Each rectangle must not exceed the width of the plate (IT IS AN IMPLIED CONSTRAINT)
constraint forall(i in 1..n) (coordsX[i]+dimsX[i]<=w);
%constraint forall(i in 1..n) (coordsY[i]+dimsY[i]<=l);
% The length of the plate is the maximum height reached (IT IS AN IMPLIED CONSTRAINT)
constraint l = max(i in 1..n)(coordsY[i]+dimsY[i]);


%%%%%%% SOLVING

% Variables selection heuristic: first the coordsX, then the coordsY; the coordsX are sorted by rectangles width, the coordsX are 
% sorted by rectangles height.
% Variables order: coordX of the rectangle with max width; coordX of the rectangle with second max width; ... ; coordY of the rectangle
% with max height; coordY of the rectangle with second max height; ... . 
ann: search_annY = int_search(reverse(sort_by(coordsY, dimsY)), input_order, indomain_min);
ann: search_annX = int_search(reverse(sort_by(coordsX, dimsX)), input_order, indomain_min);

solve :: seq_search([search_annY, search_annX]) 
minimize l;