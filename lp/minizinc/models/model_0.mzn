%---------------------------------------------------------------------------------------------------------------------------%
%                                                         MODEL 0                                                           %
% First base interpretation of the problem that does not make use of global constraints.                                    %
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

/** X coordinate of the bottom-left corner of the circuits. */
array[1..n] of var 0..l_max-h_min: coordsY;
/** Y coordinate of the bottom-left corner of the circuits. */
array[1..n] of var 0..w-w_min: coordsX;

%%%%%%% SOLVING
solve minimize l;

%%%%%%% SUCH THAT
% Constraints guaranteeing that all the circuits are within the bound of the plate.
constraint forall(i in 1..n)(coordsX[i] + dimsX[i] <= w);
constraint forall(i in 1..n)(coordsY[i] + dimsY[i] <= l);

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
