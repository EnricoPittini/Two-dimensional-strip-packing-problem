# Models recap
Here is the list of the LP models, with the corresponding brief explanation.

## Constraint Based Approach
0. The `model_0` is the basic Constraint Based approach implementation: it simply applies all the necessary condstraints in an LP formulation.
1. The `model_1` is the same as the previous one, although some improvements occur. Variable `b` that traces the non-overlapping constraint relaxations is halved in spatial complexity and the upper and lower bounds for `l` (`lMin` and `lMax`) are improved. The model presents improvements over the previous one and is the best version for the Constraint Based approach with no rotation
2. The `model_2` is the same as the previous one, with the addition of a symmetry breaking constraint that places the circuit with the greatest area in the bottom-left corner. The model performs worse than the previous one and has been therefore discarded.
3. The **rotation** variant is solved with `model_r_0`, which applies some edits to `model_1` in order to allow the rotation of the circuits.

## Position and Covering Approach
0. The `model_grid` is the Position and Covering Approach implementation: it returns the position of each circuit according to their sets of valid positions in a way that they do not overlap and are in bound of the plate.
1. The **rotation** variant is solved with `model_r_grid`, which applies some edits to `model_grid` in order to allow the rotation of the circuits.
