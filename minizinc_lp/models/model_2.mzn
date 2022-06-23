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

array[0..l_max-1, 0..w-1] of var 0..n: grid; % Grid of actual positions of each circuit

array[1..n] of var 0..l_max-h_min: coordsY;  % Coords X of the left-bottom corner of the rectangles
array[1..n] of var 0..w-w_min: coordsX;  % Coords Y of the left-bottom corner of the rectangles

%%%%%%% SOLVING
solve minimize l;

%%%%%%% SUCH THAT
% All different except 0 (guarantees all circuits are placed just one time in the grid).
constraint forall(k in 1..n)(sum(i in 0..l_max-1,j in 0..w-1)(grid[i,j] = k) = 1);
% Each circuit must be placed exactly one time in the grid.
%constraint forall(i in 1..n)(valid_positions[i, actual_positions[i]] = 1);

% No-overlap
%constraint forall(i,j in 1..n where i<j)(actual_positions[i] + w * dimsY[i] < actual_positions[j]);
array[1..n, 1..n, 1..4] of var 0..1: b;
%constraint forall(i in 0..l_max-1, j1 in 0..w-1, j2 in 0..w-1 where grid[i,j1] != 0 /\ grid[i,j2] != 0)(j1 + dimsX[grid[i,j1]] <= j2);
%constraint forall(i1 in 1..l, i2 in 1..l, j in 1..w where grid[i1,j] != 0 /\ grid[i2,j] != 0)(i1 - dimsY[grid[i1,j]] >= i2);
constraint forall(i in 0..l_max-1, j1 in 0..w-1, j2 in 0..w-1 where grid[i,j1] < grid[i,j2] /\ grid[i,j1] != 0 /\ grid[i,j2] != 0)
  (j1 + dimsX[grid[i,j1]] <= j2 + w*(1 - b[grid[i,j1],grid[i,j2],1]));

constraint forall(i1 in 0..l_max-1, i2 in 0..l_max-1, j in 0..w-1 where grid[i1,j] < grid[i2,j] /\ grid[i1,j] != 0 /\ grid[i2,j] != 0)
  (i1 <= i2 - dimsY[grid[i1,j]] + l_max*(1 - b[grid[i1,j],grid[i2,j],2]));

constraint forall(i in 0..l_max-1, j1 in 0..w-1, j2 in 0..w-1 where grid[i,j1] < grid[i,j2] /\ grid[i,j1] != 0 /\ grid[i,j2] != 0)
  (j2 + dimsX[grid[i,j2]] <= j1 + w*(1 - b[grid[i,j1],grid[i,j2],3]));

constraint forall(i1 in 0..l_max-1, i2 in 0..l_max-1, j in 0..w-1 where grid[i1,j] < grid[i2,j] /\ grid[i1,j] != 0 /\ grid[i2,j] != 0)
  (i2 <= i1 - dimsY[grid[i2,j]] + l_max*(1 - b[grid[i1,j],grid[i2,j],4]));

% At most one vertical or horizontal relation should be implied.
constraint forall(i,j in 1..n where i<j)(b[i,j,1] + b[i,j,3] <= 1);
constraint forall(i,j in 1..n where i<j)(b[i,j,2] + b[i,j,4] <= 1);
% At least one of the above constraint must be active (not relaxed) for all the coordinates i,j.
constraint forall(i,j in 1..n where i<j)(sum(b[i,j,..]) >= 1);

% In bound
constraint forall(i in 0..l_max-1, j in 0..w-1 where grid[i,j] != 0)(j + dimsX[grid[i,j]] <= w);
constraint forall(i in 0..l_max-1, j in 0..w-1 where grid[i,j] != 0)(i - dimsY[grid[i,j]] >= 1);
constraint forall(i in 0..l_max-1, j in 0..w-1 where grid[i,j] != 0)(i <= l);

% TODO Remove
constraint forall(i in 0..l_max-1, j in 0..w-1 where grid[i,j] != 0)(coordsX[grid[i,j]] = j /\ coordsY[grid[i,j]] = l - i - 1);
