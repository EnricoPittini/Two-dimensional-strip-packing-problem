%000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000|

include "cumulative.mzn";
include "diffn.mzn";
include "globals.mzn";


%%%%%%% PARAMETERS
int: w;  % The width of the plate
int: n;  % Number of the rectangles
array[1..n, 1..2] of int: dims;  % Dims X (i.e. width) and Y (i.e. height) of the rectangles
array[1..n] of int: dimsX = col(dims,1);
array[1..n] of int: dimsY = col(dims,2);

opt 0..7: symmetry_breaking_option;

array [1..n] of int: areas = [dimsX[i]*dimsY[i] | i in 1..n];  % The areas of the rectangles
int: A_tot = sum(areas);  % The overall area of all the given rectangles
int: h_min = min(dimsY);  % The minimum height of a rectangle
int: h_max = max(dimsY);  % The maximum height of a rectangle
int: w_min = min(dimsX);  % The minimum width of a rectangle
int: w_max = max(dimsX);  % The maximum width of a rectangle
int: l_min = max([h_max, A_tot div w]);  % The lower bound for the length
int: max_rects_per_row = w div w_max; % Maximum number of rectangles per row
int: max_rects_per_col = ceil(n / max([1, max_rects_per_row])); % Maximum number of rectangles per column
%int: l_max = sum(sort(dimsY)[n-max_rects_per_col+1..n]);  % The upper bound for the length

/*for i in 1..max_rects_per_col:
  count = count + sort(dimsY[1 + max_rects_per_row * (i-1)])
l_max = count;*/

int: l_max = if max_rects_per_row = 1 
  then sum(areas) 
  else sum([dimsY[k] | k in 1..n where k mod max_rects_per_row = 1])  % The upper bound for the length
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
% Symmetry breaking constraint in which for all pairs of rectangles i, j having the same dimension a lexicographic order is
% imposed between the coordinates of i and j:
%    - the array that has to be lexicographically less than the other is the one containing the coordinates of i
%    - the array that has to be lexicographically greater or equal than the other is the one containing the coordinates of j
constraint let{int: w_half = ceil(w/2)} in (sum([areas[i] | i in 1..n where coordsX[i] >= w_half]) <= A_tot / 2);
  
constraint sum([areas[i] | i in 1..n where coordsY[i] > l div 2]) <= A_tot / 2;
%constraint
%  let {array[1..n] of int: sorted_rects = reverse(sort_by(1..n, areas));}
%  in lex_less([coordsX[sorted_rects[1]], coordsY[sorted_rects[1]]], [coordsX[sorted_rects[1]], coordsY[sorted_rects[1]]]);


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
/*
solve :: seq_search([
  int_search([l], input_order, indomain_min, complete),
  int_search([coordsY[i] | i in reverse(arg_sort(areas))], input_order, indomain_min, complete),
  int_search([coordsX[i] | i in reverse(arg_sort(areas))], input_order, indomain_min, complete)
]) minimize l;
*/
solve minimize l; % :: int_search([l], input_order, indomain_min, complete)

% SYMM
%constraint forall(i,j in 1..n where i < j /\ dimsX[i] = dimsX[j] /\ dimsY[i] = dimsY[j])(
%  lex_lesseq([coordsX[i], coordsY[i]], [coordsX[j], coordsY[j]])
%);

%constraint 
%  forall(i in 1..n)(
%    member([0] ++ [coordsX[o] + dimsX[o] | o in 1..n where o != i], coordsX[i]) /\
%    member([0] ++ [coordsY[o] + dimsY[o] | o in 1..n where o != i], coordsY[i])
%  );
