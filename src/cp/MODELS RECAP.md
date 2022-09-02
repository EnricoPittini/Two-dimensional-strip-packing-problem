# Models recap
Here is the list of the CP encodings, with the corresponding brief explanation.

## No rotation models
0. The `model_0`'s architecture is naive: it applies simple "hand-written" constraints in order for the circuits to not be overlapping and to be in bounds of the plate. The lower bound of the length `l` is `l_min = max([h_max, A_tot div w])` and the upper bound of `l` is `l_max = sum(dimsY)`.
1. The `model_1` adds two new global constraints: *cumulative* constraint `cumulative(coordsX, dimsX, dimsY, l)` and cumulative constraint `cumulative(coordsY, dimsY, dimsX, w)`. They are **implied constraints** of the constraints "Non-exceeding width of the plate".
2. The `model_2` updates the upper bound of each `coordsY`: `l_max`. A new global *diffn* constraint `diffn(coordsX, coordsY, dimsX, dimsY)`. The "Non-overlapping constraint is removed
3. In this group of models, i.e. encodings from `model_3A` to `model_3C`, different combinations of the implied constraints (*cumulative constraints*) are tested. In the end `model_3B` that keeps only `cumulative(coordsX, dimsX, dimsY, l)` was the best model.
4. In this group of models, i.e. encodings from `model_4A0` to `model_4A7`, the value of `l_max` was improved, along with the upper bound of `coordsX` ("w-w_min") and the upper bound of `coordsy` ("l_max-h_min"). Combinations of the following constraints are tested:
	- Lexicographic order on the coordinates of rectangles having the same dimension;
	- The area of the rectangles on the right half of the plate is less or equal than half the total area of the rectangles;
	- The area of the rectangles on the top half of the plate is less or equal than half the total area of the rectangles.

	In the end, `model_4A4` containing just the last two was kept.
	Models from `model_4B0` to model `model_4C2` contain other discarded heuristics.
5. The `model_5` adds another view of the problem creating a dual model.
Defines a grid of the dimension of the plate in which in each cell it is expressed which rectangle is present (from 1 to n)
or 0 if no rectangle is present. It was discarded because of poor performances.
6. In this group of models, i.e. encodings from `model_6A` to `model_6G`, different search heuristics are exploited. A heuristic that always select the lowest possible value in the domain of the length of the plate `l` is always used. Other heuristics are tested:
	- Variables selection heuristic based on: the rectangles areas.
	- Variables selection heuristic based on: the rectangles width.
	- Variables selection heuristic based on: the rectangles height.
	- Gecode "dom_w_deg" and luby search heuristics.

	Finally, `model_6D1` is chosen as the final model. It applies an ordered search on the interleaved `coordsX` and `coordsY` of the circuits sorted by decreasing order with respect to the value of their width.

## Rotation models
0. The `model_r_0` uses the structure of `model_6D1`, removing the search heuristics and applying (and editing) the necessary constraints and variables in order to account for rotations of the circuits.
1. In this group of models, i.e. encodings from `model_r_1A` to `model_r_1D`, different combinations of the implied constraints (*cumulative constraints*) are tested again. In the end `model_r_1B` that keeps, again, only `cumulative(coordsX, actualDimsX, actualDimsY, l)` was the best model.
2. In this group of models, i.e. encodings from `model_r_2A` to `model_r_2B`, the domains restriction for the actual dimension arrays of the circuits was tested, furthermore `model_r_2B` adds a constraint regarding the relation between the orientation and the actual dimensions of the circuits and performs better, so it was kept.
3. In this group of models, i.e. encodings from `model_r_3A` to `model_r_3B`, the following constraints were tested:
	- If a circuit does not fit in an orientation it should be rotated to the other;
	- If circuits do not fit one on top of the other they must stay side by side;
    - If circuits do not fit one on the side of the other they must stay one on top of the other.

	None of them performed better, so the models were discarded
4. In this group of models, i.e. encodings from `model_r_4A` to `model_r_4H`, different combinations of the following symmetry breaking constraints were tested:
	- Squared circuits should not be rotated;
	- Circuits with the same actual respective dimensions are lexicogrphically ordered;
	- Circuits on the same column should follow just one of the possible permutations;
	- Circuits on the same row should follow just one of the possible permutations.    

	None of them performed better, so the models were discarded.
5. In this group of models (`model_r_5*`) different combinations of the constraint at the previous point were tested, while removing the symmetry breaking constraints introduced far back in model `model_4A4`. All of them were discarded.
6. The `model_r_6` uses the structure of `model_r_2B` and applies Generalised Arc Consistency (GAC) on the constraints. Since it does not improve the performances it was dscarded.
7. In this group of models, i.e. encodings from `model_7A` to `model_7G`, different search heuristics are exploited. A heuristic that always select the lowest possible value in the domain of the length of the plate `l` is always used. Other heuristics are tested:
	- Variables selection heuristic based on: the rectangles areas.
	- Variables selection heuristic based on: the rectangles maximum dimension.
	- Heuristic choosing the orientation of rectangles with biggest area or maximum dimension first. 
	
	Finally, `model_r_7B` is chosen as the final model. It determines the rotation of the circuits by decreasing order with respect to their areas. Then applies an ordered search on the interleaved `coordsX` and `coordsY` of the circuits sorted by decreasing order with respect to the value of their maximum dimension.