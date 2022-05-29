%---------------------------------------------------------------------------------------------------------------------------%
%                                                      MODEL 4B1                                                            %
%                                                                                                                           %
% Model that uses the best symmetry breaking combination of the model 4A and adds a symmetry breaking constraint that:      %
% - Puts the rectangle with the greatest area on the bottom left corner.                                                    %
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
int: h_min = min(dimsY);  % The minimum height of a rectangle
int: h_max = max(dimsY);  % The maximum height of a rectangle
int: w_min = min(dimsX);  % The minimum width of a rectangle
int: w_max = max(dimsX);  % The maximum width of a rectangle
int: l_min = max([h_max, A_tot div w]);  % The lower bound for the length
int: max_rects_per_row = w div w_max; % Maximum number of rectangles per row
int: max_rects_per_col = ceil(n / max([1, max_rects_per_row])); % Maximum number of rectangles per column
% The upper bound for the length
int: l_max = if max_rects_per_row = 1 
  then sum(areas) 
  else sum([dimsY[k] | k in 1..n where k mod max_rects_per_row = 1]) 
endif;

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

% Each rectangle must not exceed the width of the plate (IT IS AN IMPLIED CONSTRAINT)
constraint forall(i in 1..n) (coordsX[i]+dimsX[i]<=w);
% The length of the plate is the maximum height reached (IT IS AN IMPLIED CONSTRAINT)
constraint l = max(i in 1..n)(coordsY[i]+dimsY[i]);


%%%%%%% SYMMETRY BREAKING
% Symmetry breaking constraint in which for all pairs of rectangles i, j having the same dimension a lexicographic order is
% imposed between the coordinates of i and j:
%    - the array that has to be lexicographically less than the other is the one containing the coordinates of i
%    - the array that has to be lexicographically greater or equal than the other is the one containing the coordinates of j
constraint forall(i,j in 1..n where i < j /\ dimsX[i] = dimsX[j] /\ dimsY[i] = dimsY[j])(
  lex_lesseq([coordsX[i], coordsY[i]], [coordsX[j], coordsY[j]])
);

constraint let{int: w_half = ceil(w/2)} in (sum([areas[i] | i in 1..n where coordsX[i] >= w_half]) <= A_tot / 2);
  
constraint (sum([areas[i] | i in 1..n where coordsY[i] > l div 2]) <= A_tot / 2);

constraint coordsX[arg_max(areas)] = 0 /\ coordsY[arg_max(areas)] = 0;

%%%%%%% SOLVING
solve minimize l;