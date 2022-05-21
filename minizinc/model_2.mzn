%000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000|

include "cumulative.mzn";
include "diffn.mzn";


%%%%%%% PARAMETERS
int: w;  % The width of the plate
int: n;  % Number of the rectangles
array[1..n, 1..2] of int: dims;  % Dims X (i.e. width) and Y (i.e. height) of the rectangles
array[1..n] of int: dimsX = col(dims,1);
array[1..n] of int: dimsY = col(dims,2);

int: A_tot = sum(i in 1..n)(dimsX[i]*dimsY[i]);  % The overall area of all the given rectangles
int: h_max = max(dimsY);  % The maximum height of a rectangle
int: l_min = max([h_max, A_tot div w]);  % The lower bound for the length
int: l_max = sum(dimsY);  % The upper bound for the length


%%%%%%% VARIABLES
% The length of the plate
var l_min..l_max: l;

% NEW UPPER BOUND FOR COORDSY
array[1..n] of var 0..l_max: coordsY;  % Coords X of the left-bottom corner of the rectangles
array[1..n] of var 0..w: coordsX;  % Coords Y of the left-bottom corner of the rectangles


%%%%%%% CONSTRAINTS 
% NEW GLOBAL CONSTRAINT
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
% The length of the plate is the maximum height reached (IT IS AN IMPLIED CONSTRAINT)
constraint l = max(i in 1..n)(coordsY[i]+dimsY[i]);


%%%%%%% SOLVING
solve minimize l;