# Model 0
- Lower bound of the length `l`: l_min = max([h_max, A_tot div w])
- Upper bound of the length `l`: l_max = sum(dimsY)
- Non-overlapping constraint: hand-written forall constraint (quite ineficcient)
- Non-exceeding width of the plate: hand-written forall constraint
- Definition of `l` constraint: maximum height reached

### Instances
Instance 8: Gecode exceeded 5 minutes; Chuffed 31 seconds.

# Model 1
- **New global constraint**: Cumulative constraint `cumulative(coordsX, dimsX, dimsY, l)`
- **New global constraint**: Cumulative constraint `cumulative(coordsY, dimsY, dimsX, w)`
- They are **implied constraints** of the constraints "Non-exceeding width of the plate" and "Definition of `l` constraint"

### Instances
Instance 8: Gecode 252 ms; Chuffed 360 ms.
Instance 12: Gecode 3.86 s; Chuffed 0.44 s.
Instance 13: Gecode 3.77 s; Chuffed 0.44 s.
Instance 16: Chuffed 3.39 s.
Instance 22: Chuffed exceed 5 minutes.

# Model 2
- Upper bound of each `coordsY`: `l_max`
- **New global constraint**: diffn constraint `diffn(coordsX, coordsY, dimsX, dimsY)`
- Removed the "Non-overlapping constraint"

### Instances
Instance 13: Gecode 0.29 s; Chuffed 0.45 s.
Instance 16: exceed 5 minutes; Chuffed 4.47 s.
Instance 22: Chuffed 1.53 s.
Instance 24: Chuffed 1.56 s.
Instance 25: Chuffed exceed 5 minutes.
Instance 28: Chuffed 23.11 s.

# Model 3
Testing the implied constraints (*cumulative constraints*)
- 3A. Kept only `cumulative(coordsY, dimsY, dimsX, w)`.
- 3B. ☑ Kept only `cumulative(coordsX, dimsX, dimsY, l)`.
- 3C. Removed both *cumulative constraints*.
In the end 3B was the best model (see *cumulative_results_i.json* files).

# Model 4A
Improved variable bounds.
- improved `l_max`.
- improved upper bound of `coordsX` "w-w_min"
- improved upper bound of `coordsy` "l_max-h_min"
Symmetry breaking constraints:
- 4A batch of models test combinations of the following constraints:
	- 1. Lexicographic order on the coordinates of rectangles having the same dimension;
	- 2. The area of the rectangles on the right half of the plate is less or equal than half the total area of the rectangles;
	- 3. The area of the rectangles on the top half of the plate is less or equal than half the total area of the rectangles;
- 4A0: tests a model withouth any among 1, 2 and 3;
- 4A1: tests 1, 2 and 3;
- 4A2: tests 1 and 2;
- 4A3: tests 1 and 3;
- 4A4 ☑: tests 2 and 3;
- 4A5: tests 1;
- 4A6: tests 2;
- 4A7: tests 3.

4A4 and 4A1 had the best results and pretty similar ones. 4A4 has been chosen since it is more "lightweight".

# Model 4B
Symmetry breaking constraints:
4B batch of models use the best symmetry breaking combination found in the batch 4A (4A4) and selects one of the following constraints:
- 4B0: puts the highest rectangle on the bottom left corner;
- 4B1: puts the rectangle with the greater area on the bottom left corner;
- 4B2: puts the widest rectangle on the bottom left corner.

### Instances
Instance 25: Chuffed 275.54 s (and 257.33 s). (HEURISTIC BY HEIGTH BOTH COORDX AND COORDY)
Instance 25: Chuffed time exceeded. (HEURISTIC BY HEIGTH INTERLEAVING COORDX AND COORDY)
Instance 25: 0.82 s. (HEURISTIC BY WIDTH INTERLEAVING COORDX AND COORDY)
Instance 26: Chuffed 2.16 s. (FIRST FAIL HEURISTIC)
Instance 26: Chuffed time exceeded. (HEURISTIC BY WIDTH INTERLEAVING COORDX AND COORDY)
Instance 26: Chuffed time exceeded. (HEURISTIC BY AREA INTERLEAVING COORDX AND COORDY)
Instance 26: Chuffed 0.32 s. (HEURISTIC BY HEIGTH COORDY AND HEURISTIC BY WIDTH COORDX)
Instance 28: Chuffed 43.68 s. (FIRST FAIL HEURISTIC)
Instance 28: Chuffed 0.32 s (and 2.44 s).  (HEURISTIC BY HEIGTH BOTH COORDX AND COORDY)

# Model 7
Adds another view of the problem creating a dual model.
Defines a grid of the dimension of the plate in which in each cell it is expressed which rectangle is present (from 1 to n)
or 0 if no rectangle is present.
Constraints:
- In each row each rectangle either completely fits in or is not in the row;
- In each column each rectangle either completely fits in or is not in the column;
- Channeling constraint imposing that each cell of the grid containing a rectangle label `k` has:
	- the second index of the cell between `coordX` and `coordX` + `dimsX` of the rectangle `k`;
	- the first index of the cell between `coordY` and `coordY` + `dimsY` of the rectangle `k`.

Symmetry breaking constraints:
- for identical rectangles.

<!-- TODO: Update once done. -->
# Model 8
New variables selection heuristic 
- 8A. Variables selection heuristic based on: the rectangles areas; it interleaves coordX and coordY.
- 8B. Variables selection heuristic based on: the rectangles width; it interleaves coordX and coordY.
- 8C. Variables selection heuristic: first the coordsX, then the coordsY; the coordsX are sorted by rectangles width, the 
coordsX are sorted by rectangles height.

# Model 8 (Geocode specific)
- Variables selection heuristic specific for Geocode: dom_w_deg, restarting (luby) with random values selection heuristic,LNS
