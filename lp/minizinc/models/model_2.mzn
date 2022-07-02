%---------------------------------------------------------------------------------------------------------------------------%
%                                                         MODEL 2                                                           %
%  Grid-based model.                                                                                                        %
%---------------------------------------------------------------------------------------------------------------------------%


%%%%%%% INPUT PARAMETERS
/** The width of the plate. */
int: w;
/** The number of the circuits. */
int: n;
/** Dimensions of the circuits. */
array[1..n, 1..2] of int: dims;

%%%%%%% DERIVED PARAMETERS
/** Widths of the circuits. */
array[1..n] of int: dimsX = col(dims,1);
/** Heights of the circuits. */
array[1..n] of int: dimsY = col(dims,2);

/** Areas of the circuits. */
array [1..n] of int: areas = [dimsX[i]*dimsY[i] | i in 1..n];
/** The overall area of all the given circuits. */
int: A_tot = sum(areas);

/** The minimum height among the circuits. */
int: h_min = min(dimsY);
/** The maximum height among the circuits. */
int: h_max = max(dimsY);

/** The minimum width among the circuits. */
int: w_min = min(dimsX);
/** The maximum width among the circuits. */
int: w_max = max(dimsX);

/** The lower bound for the length of the plate. */
int: l_min = max([h_max, A_tot div w]);

/** Minimum number of circuits per row. */
int: min_rects_per_row = w div w_max;
/** The upper bound for the length of the plate. */
int: l_max = if min_rects_per_row = 1 
  then sum(dimsY) 
  else let{array [1..n] of int: sorted_dimsY = reverse(sort(dimsY))} in 
    sum([sorted_dimsY[k] | k in 1..n where k mod min_rects_per_row = 1]) 
endif;

%%%%%%% VARIABLES
/** The length of the plate. */
var l_min..l_max: l;

/** Grid of coordinates of each circuit. */
array[0..l_max, 0..w] of var 0..n: grid; 

/** Y coordinate of the bottom-left corner of the circuits. */
array[1..n] of var 0..l_max-h_min: coordsY;
/** X coordinate of the bottom-left corner of the circuits. */
array[1..n] of var 0..w-w_min: coordsX;

%%%%%%% SOLVING
solve minimize l;

%%%%%%% SUCH THAT
% Guarantees all circuits are placed just one time in the grid completely.
constraint forall(k in 1..n)(sum(i in 0..l_max-1,j in 0..w-1)(grid[i,j] = k) = areas[k]);

% The circuits cannot get split over a row or a column
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
constraint forall(k in 1..n, i in 0..l_max, j in 0..w)(adjacent_circuits_in_rows[k, i, j] <= (grid[i,j] = k)*dimsX[k]);

constraint forall(k in 1..n, i in 0..w, j in 1..l_max)
  (adjacent_circuits_in_columns[k, i, j-1] + 1 - (1 - (grid[j,i] = k))*l_max <= adjacent_circuits_in_columns[k, i, j]);
constraint forall(k in 1..n, i in 0..w, j in 1..l_max)
  (adjacent_circuits_in_columns[k, i, j] <= adjacent_circuits_in_columns[k, i, j-1] + 1 + (1 - (grid[j,i] = k))*l_max);
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
constraint forall(k in 1..n, i in 0..l_max, j in 0..w)(count_of_circuits_in_rows[k,i,j] = dimsX[k] * (count_of_circuits_in_rows[k,i,j] != 0));
constraint forall(k in 1..n, i in 0..w, j in 0..l_max)(count_of_circuits_in_columns[k,i,j] = dimsY[k] * (count_of_circuits_in_columns[k,i,j] != 0));

% Grid boundary constraints.
constraint forall(i in l..l_max, j in 0..w)(grid[i,j] = 0); % THESE ARE FINE
constraint forall(i in 0..l_max)(grid[i,w] = 0); % THESE ARE FINE

% Channeling constraint.
constraint forall(k in 1..n)(coordsX[k] = min([j | i in 0..l_max, j in 0..w where grid[i,j] = k]));
constraint forall(k in 1..n)(coordsY[k] = l - max([i | i in 0..l_max, j in 0..w where grid[i,j] = k]));
