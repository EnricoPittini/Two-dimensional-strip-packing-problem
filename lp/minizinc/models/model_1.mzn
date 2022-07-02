%---------------------------------------------------------------------------------------------------------------------------%
%                                                         MODEL 1                                                           %
% Model that adds a grid of valid positions for each circuit before solving the problem.                                    %
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

/** Y coordinate of the bottom-left corner of the circuits. */
array[1..n] of var 0..l_max-h_min: coordsY;
/** X coordinate of the bottom-left corner of the circuits. */
array[1..n] of var 0..w-w_min: coordsX;

/** Grid of valid positions for each circuit. */
array[1..n, 0..l_max-1, 0..w-1] of var 0..1: valid_positions = 
  array3d(1..n, 0..l_max-1, 0..w-1, 
    [if (i + dimsY[k] <= l /\ j + dimsX[k] <= w) then 1 else 0 endif | k in 1..n, i in 0..l_max-1, j in 0..w-1]); 

%%%%%%% SOLVING
solve minimize l;

%%%%%%% SUCH THAT
% The circuit is in a valid position.
constraint forall(i in 1..n)(valid_positions[i, coordsY[i], coordsX[i]] >= 1);

% Non-overlapping constraints.
/** Binary variables for each coordinate i,j related to the non-overlapping constraints. */
array[1..n, 1..n, 1..4] of var 0..1: b;
/** Big-M technique. */
int: M = 1000000;
/* If a constraint is active b[i,j,k] = 1 then the circuits must not overlap in the given dimension.
Otherwise (the constraint is not active b[i,j,k] = 0), the constraint will always be satisfied thanks to the Big-M technique 
and the overlapping in the given dimension will be ignored. */
constraint forall(i,j in 1..n where i<j)(coordsX[i] + dimsX[i] <= coordsX[j] + M*(1 - b[i,j,1]));
constraint forall(i,j in 1..n where i<j)(coordsY[i] + dimsY[i] <= coordsY[j] + M*(1 - b[i,j,2]));
constraint forall(i,j in 1..n where i<j)(coordsX[j] + dimsX[j] <= coordsX[i] + M*(1 - b[i,j,3]));
constraint forall(i,j in 1..n where i<j)(coordsY[j] + dimsY[j] <= coordsY[i] + M*(1 - b[i,j,4]));
% At most one vertical or horizontal relation should be implied.
constraint forall(i,j in 1..n where i<j)(b[i,j,1] + b[i,j,3] <= 1);
constraint forall(i,j in 1..n where i<j)(b[i,j,2] + b[i,j,4] <= 1);
% At least one of the above constraint must be active (not relaxed) for all the coordinates i,j.
constraint forall(i,j in 1..n where i<j)(sum(b[i,j,..]) >= 1);
