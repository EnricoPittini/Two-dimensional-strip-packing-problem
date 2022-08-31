%---------------------------------------------------------------------------------------------------------------------------%
%                                                        MODEL 1                                                            %
%                                                                                                                           %
% Model that uses the global `cumulative` constraints.                                                                      %
%---------------------------------------------------------------------------------------------------------------------------%

include "cumulative.mzn";


%%%%%%% PARAMETERS
/** The width of the plate */
int: w;
/** Number of circuits */
int: n;
/** Matrix containing for each circuit its dimensions (width and height) */
array[1..n, 1..2] of int: dims;
/** Derived width of the circuits */
array[1..n] of int: dimsX = col(dims,1);
/** Derived height of the circuits */
array[1..n] of int: dimsY = col(dims,2);

/** The overall area of all the given circuits */
int: A_tot = sum(i in 1..n)(dimsX[i]*dimsY[i]);
/** The maximum height of a circuit */
int: h_max = max(dimsY);
/** The lower bound for the length */
int: l_min = max([h_max, A_tot div w]);
/** The upper bound for the length */
int: l_max = sum(dimsY);


%%%%%%% VARIABLES
/** The length of the plate */
var l_min..l_max: l;
/** X coordinate of the left-bottom corner of the circuits */
array[1..n] of var 0..w: coordsX;
/** Y coordinate of the left-bottom corner of the circuits */
array[1..n] of var 0..1000: coordsY;


%%%%%%% CONSTRAINTS 
% The circuits must be non-overlapping
constraint forall(i,j in 1..n where i<j)
  ((coordsX[i]+dimsX[i]<=coordsX[j] \/ coordsX[j]+dimsX[j]<=coordsX[i]) \/
  (coordsY[i]+dimsY[i]<=coordsY[j] \/ coordsY[j]+dimsY[j]<=coordsY[i]));

% TWO NEW GLOBAL CONSTRAINTS
% Cumulative implied constraint in which:
%    - the starting times of the tasks are coordsX
%    - the durations of the tasks are dimsX
%    - the resource recquirements of the tasks are dimsY
%    - the maximum resource bound is l
constraint cumulative(coordsX, dimsX, dimsY, l);
% Cumulative implied constraint in which:
%    - the starting times of the tasks are coordsY
%    - the durations of the tasks are dimsY
%    - the resource recquirements of the tasks are dimsX
%    - the maximum resource bound is w
constraint cumulative(coordsY, dimsY, dimsX, w);

% Each circuit must not exceed the width of the plate
constraint forall(i in 1..n) (coordsX[i]+dimsX[i]<=w);
% The length of the plate is the maximum height reached
constraint l = max(i in 1..n)(coordsY[i]+dimsY[i]);


%%%%%%% SOLVING
solve minimize l;
