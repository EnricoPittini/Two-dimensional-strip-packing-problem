%---------------------------------------------------------------------------------------------------------------------------%
%                                                         MODEL 02                                                          %
% Duality                                                                                                                   %
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

array[1..n] of var 0..l_max-h_min: coordsY;  % Coords X of the left-bottom corner of the rectangles
array[1..n] of var 0..w-w_min: coordsX;  % Coords Y of the left-bottom corner of the rectangles


%%%%%%% SOLVING
solve minimize l;

%%%%%%% SUCH THAT
% In bound
/** Slack variables for constraint regarding the in boundness on the width of the plate. */
array [1..n] of var 0..w: slack_in_bound_w;
constraint forall(i in 1..n)(coordsX[i] + slack_in_bound_w[i] = w - dimsX[i]); % (1)

/** Slack variables for constraint regarding the in boundness on the length of the plate. */
array [1..n] of var 0..l_max: slack_in_bound_l;
constraint forall(i in 1..n)(coordsY[i] + slack_in_bound_l[i] - l = 0 - dimsY[i]); % (2)

% Non overlapping
/** Binary variables for each coordinate i,j related to the non-overlapping constraints. */
array[1..n, 1..n, 1..4] of var 0..1: b;
% Guarantee that the symmetric part of the 4 matrices over the diagonal has all zeroes.  
constraint forall(i,j in 1..n where i >= j, k in 1..4)(b[i,j,k] = 0); % (3)

/** Slack variables for each constraint regarding the non overlapping. */
array[1..n, 1..n, 1..4] of var 0..max([w,l_max]): slack_non_overlapping;
% Guarantee that the symmetric part of the 4 matrices over the diagonal has all zeroes.  
constraint forall(i,j in 1..n where i >= j, k in 1..4)(slack_non_overlapping[i,j,k] = 0); % (4)

% If a constraint is active b[i,j,k] = 1 then the circuits must not overlap in the given dimension.
% Otherwise (the constraint is not active b[i,j,k] = 0). In practice the constraint will always be satisfied thanks to
% the Big-M trick and the overlapping in the given dimension will be ignored.
constraint forall(i,j in 1..n where i<j)(coordsX[i] + 0*coordsX[j] + w*b[i,j,1] + slack_non_overlapping[i,j,1] - coordsX[j] = 0 - dimsX[i] + w); % (5)
constraint forall(i,j in 1..n where i<j)(coordsY[i] + 0*coordsX[j] + l_max*b[i,j,2] + slack_non_overlapping[i,j,2] - coordsY[j] = 0 - dimsY[i] + l_max); % (6)
constraint forall(i,j in 1..n where i<j)(0*coordsX[i] + coordsX[j] + w*b[i,j,3] + slack_non_overlapping[i,j,3] - coordsX[i] = 0 - dimsX[j] + w); % (7)
constraint forall(i,j in 1..n where i<j)(0*coordsY[i] + coordsY[j] + l_max*b[i,j,4] + slack_non_overlapping[i,j,4] - coordsY[i] = 0 - dimsY[j] + l_max); % (8)
% At most one vertical or horizontal relation should be implied.
% constraint forall(i,j in 1..n where i<j)(b[i,j,1] + b[i,j,3] <= 1);
% constraint forall(i,j in 1..n where i<j)(b[i,j,2] + b[i,j,4] <= 1);

% At least one of the above constraint must be active (not relaxed) for all the coordinates i,j.
/** Slack variable regarding the activation of the non-overlapping constraints */
array[1..n, 1..n] of var 0..1: slack_non_overlapping_activation;
constraint forall(i,j in 1..n where i<j)(sum(b[i,j,..]) - slack_non_overlapping_activation[i,j] = 1); % (9)

%%% TRANSPOSITION TO GET THE DUAL
% In bound
/** Slack variables for constraint regarding the in boundness on the width of the plate. */
array [1..n] of var 0..w: y_bound_w; % (1)

/** Slack variables for constraint regarding the in boundness on the length of the plate. */
array [1..n] of var 0..l_max: y_bound_l; % (2)
% constraint forall(i in 1..n)(coordsY[i] + dimsY[i] + slack_in_bound_l[i] = l);

% Non-overlapping
array [1..n, 1..n, 1..4] of var 0..w: y_symmetry_b; % (3)
array [1..n, 1..n, 1..4] of var 0..w: y_symmetry_slack_non_overlapping; % (4)

/** Slack variables for each constraint regarding the non overlapping. */
array[1..n, 1..n, 1..4] of var 0..1: y_non_overlapping; % (5 ,6, 7, 8)
/** Slack variable regarding the activation of the non-overlapping constraints */
array[1..n, 1..n] of var 0..1: y_non_overlapping_activation; % (9)

% TRANSPOSED CONSTRAINTS
constraint forall(i in 1..n)(coordsX[i] = w);
