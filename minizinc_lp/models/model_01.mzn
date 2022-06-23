%---------------------------------------------------------------------------------------------------------------------------%
%                                                         MODEL 2                                                           %
%  https://journals.plos.org/plosone/article?id=10.1371/journal.pone.0245267#sec002 (covering stage)                        %
%---------------------------------------------------------------------------------------------------------------------------%


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

%array[1..n, 1..w*l] of 0..1: valid_positions = [if (j + w * dimsY[i] < w*l /\ (j mod w) + dimsX[j] < w) then 1 else 0 endif | i in 1..n, j in 1..w*l]; % Grid of valid positions for each circuit 

%array[1..w, 1..l] of 0..n: valid_positions = [if (j + w * dimsY[i] < w*l /\ (j mod w) + dimsX[j] < w) then 1 else 0 endif | i in 1..n, j in 1..w*l]; % Grid of valid positions for each circuit

% array[1..w*l] of var 1..n: actual_positions; % Grid of actual positions of each circuit

array[0..l_max, 0..w] of var 0..n: grid; % Grid of actual positions of each circuit

array[1..n] of var 0..l_max-h_min: coordsY;  % Coords X of the left-bottom corner of the rectangles
array[1..n] of var 0..w-w_min: coordsX;  % Coords Y of the left-bottom corner of the rectangles

%%%%%%% SOLVING
solve minimize l;

%%%%%%% SUCH THAT
% Guarantees all circuits are placed just one time in the grid completely.
constraint forall(k in 1..n)(sum(i in 0..l_max-1,j in 0..w-1)(grid[i,j] = k) = areas[k]);

% All rectangles appearing or not in a certain row/column.
% array[1..n, 0..l_max-1] of var 0..1: appears_in_row;
% array[1..n, 0..w-1] of var 0..1: appears_in_column;

% A circuit
% constraint forall(k in 1..n, i in 0..l_max-1)(sum(grid[i,..]) + (1 - appears_in_row[k, i]) * dimsX[k] = dimsX[k])


% A circuit `k` must appear exactly `dimsX[k]` times in a row.
% constraint forall(k in 1..n)(sum(appears_in_row[k,..]) = dimsX[k]);
% A circuit `k` must appear exactly `dimsY[k]` times in a column.
% constraint forall(k in 1..n)(sum(appears_in_column[k,..]) = dimsY[k]);

% The circuits cannot get split over a row or a column (http://yetanothermathprogrammingconsultant.blogspot.com/2018/04/a-difficult-mip-construct-counting.html).
/** Array to track adjacent units of each circuits on each row. */
array [1..n, 0..l_max, 0..w] of var 0..max(dimsX): adjacent_circuits_in_rows;
/** Array to count adjacent units of each circuits on each row. */
array [1..n, 0..l_max, 0..w] of var 0..max(dimsX): count_of_circuits_in_rows;
/** Array to track adjacent units of each circuits on each column. */
array [1..n, 0..w, 0..l_max] of var 0..max(dimsY): adjacent_circuits_in_columns;
/** Array to count adjacent units of each circuits on each column. */
array [1..n, 0..w, 0..l_max] of var 0..max(dimsY): count_of_circuits_in_columns;

% a_i
constraint forall(k in 1..n, i in 0..l_max, j in 1..w)
  (adjacent_circuits_in_rows[k, i, j-1] + 1 - (1 - (grid[i,j] = k))*w <= adjacent_circuits_in_rows[k, i, j]);
constraint forall(k in 1..n, i in 0..l_max, j in 1..w)
  (adjacent_circuits_in_rows[k, i, j] <= adjacent_circuits_in_rows[k, i, j-1] + 1 + (1 - (grid[i,j] = k))*w);
%constraint forall(k in 1..n, i in 0..l_max-1, j in 1..w-1)(0 <= adjacent_circuits_in_rows[k, i, j]);
constraint forall(k in 1..n, i in 0..l_max, j in 0..w)(adjacent_circuits_in_rows[k, i, j] <= (grid[i,j] = k)*dimsX[k]);

constraint forall(k in 1..n, i in 0..w, j in 1..l_max)
  (adjacent_circuits_in_columns[k, i, j-1] + 1 - (1 - (grid[j,i] = k))*l_max <= adjacent_circuits_in_columns[k, i, j]);
constraint forall(k in 1..n, i in 0..w, j in 1..l_max)
  (adjacent_circuits_in_columns[k, i, j] <= adjacent_circuits_in_columns[k, i, j-1] + 1 + (1 - (grid[j,i] = k))*l_max);
%constraint forall(k in 1..n, i in 0..w-1, j in 1..l_max-1)(0 <= adjacent_circuits_in_columns[k, i, j]);
constraint forall(k in 1..n, i in 0..w, j in 0..l_max)(adjacent_circuits_in_columns[k, i, j] <= (grid[j,i] = k)*dimsY[k]);  

% z_i
% rows
% z_r1
constraint forall(k in 1..n, i in 0..l_max, j in 1..w)
  (adjacent_circuits_in_rows[k, i, j-1] - (grid[i,j] = k)*w - (1 - grid[i,j-1] = k)*w <= count_of_circuits_in_rows[k,i,j]);
% z_r2
constraint forall(k in 1..n, i in 0..l_max, j in 1..w)
  (count_of_circuits_in_rows[k,i,j] <= adjacent_circuits_in_rows[k, i, j-1] + (grid[i,j] = k)*w + (1 - grid[i,j-1] = k)*w);
  
%constraint forall(k in 1..n, i in 0..l_max-1, j in 1..w)(0 <= count_of_circuits_in_rows[k,i,j]);
% z_r3
constraint forall(k in 1..n, i in 0..l_max, j in 1..w)(count_of_circuits_in_rows[k,i,j] <= (grid[i,j-1] = k)*w);
% z_r4
constraint forall(k in 1..n, i in 0..l_max, j in 0..w)(count_of_circuits_in_rows[k,i,j] <= (1 - (grid[i,j] = k))*dimsX[k]);
% constraint forall(k in 1..n, i in 0..l_max-1)(count_of_circuits_in_rows[k,i,w] <= dimsX[k]);
constraint forall(k in 1..n, i in 0..l_max-1)(count_of_circuits_in_rows[k,i,0] = 0);

% columns
% z_c1
constraint forall(k in 1..n, i in 0..w, j in 1..l_max)
  (adjacent_circuits_in_columns[k, i, j-1] - (grid[j,i] = k)*l_max - (1 - grid[j-1,i] = k)*l_max <= count_of_circuits_in_columns[k,i,j]);
% z_c2
constraint forall(k in 1..n, i in 0..w, j in 1..l_max)
  (count_of_circuits_in_columns[k,i,j] <= adjacent_circuits_in_columns[k, i, j-1] + (grid[j,i] = k)*l_max + (1 - grid[j-1,i] = k)*l_max);
  
%constraint forall(k in 1..n, i in 0..w-1, j in 1..l_max)(0 <= count_of_circuits_in_columns[k,i,j]);
% z_c3
constraint forall(k in 1..n, i in 0..w, j in 1..l_max)(count_of_circuits_in_columns[k,i,j] <= (grid[j-1,i] = k)*l_max);
% z_c4
constraint forall(k in 1..n, i in 0..w, j in 0..l_max)(count_of_circuits_in_columns[k,i,j] <= (1 - (grid[j,i] = k))*dimsY[k]);
% constraint forall(k in 1..n, i in 0..w-1)(count_of_circuits_in_columns[k,i,l_max] <= dimsY[k]);
constraint forall(k in 1..n, i in 0..w)(count_of_circuits_in_columns[k,i,0] = 0);

% Count per row and column for eac cell must be either 0 or the dimension according to the axis.
% /** Array to check that either every cell in `count_of_circuits_in_rows` is either 0 or `dimsX` of the circuit. */
% array[1..n, 0..w-1, 0..l_max] of var 0..1: counts_per_row_disjunctions;
constraint forall(k in 1..n, i in 0..l_max, j in 0..w)(count_of_circuits_in_rows[k,i,j] = dimsX[k] * (count_of_circuits_in_rows[k,i,j] != 0)); % THESE ARE FINE
constraint forall(k in 1..n, i in 0..w, j in 0..l_max)(count_of_circuits_in_columns[k,i,j] = dimsY[k] * (count_of_circuits_in_columns[k,i,j] != 0)); % THESE ARE FINE

% Every cell of the grid at row index greater or equal than `l` is 0. TODO FIX
% constraint forall(i in l..l_max)((sum(grid[i,..]) + sum(appears_in_row[..,i])) = 0);

% Grid boundary constraints.
constraint forall(i in l..l_max, j in 0..w)(grid[i,j] = 0); % THESE ARE FINE
constraint forall(i in 0..l_max)(grid[i,w] = 0); % THESE ARE FINE

% Channeling constraint
% TODO: do not exceed the board with coords
% constraint forall(i in 0..l_max-1, j in 0..w-1 where grid[i,j] != 0)(coordsX[grid[i,j]] = j /\ coordsY[grid[i,j]] = l - i - 1);
% constraint forall(k in 1..n, i in coordsY[k]..coordsY[k]+dimsY[k]-1, j in coordsX[k]..coordsX[k]+dimsX[k]-1)(grid[i,j] = k);
constraint forall(k in 1..n)(coordsX[k] = min([j | i in 0..l_max, j in 0..w where grid[i,j] = k]));
constraint forall(k in 1..n)(coordsX[k] = l - max([i | i in 0..l_max, j in 0..w where grid[i,j] = k]));