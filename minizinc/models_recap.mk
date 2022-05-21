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
- Now the constraints "Non-exceeding width of the plate" and "Definition of `l` constraint" are **implied constraints**

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
New variables selection heuristic 
- 3A. Variables selection heuristic based on: the rectangles areas; it interleaves coordX and coordY.
- 3B. Variables selection heuristic based on: the rectangles width; it interleaves coordX and coordY.
- 3C. Variables selection heuristic: first the coordsX, then the coordsY; the coordsX are sorted by rectangles width, the 
coordsX are sorted by rectangles height.

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

# Model 4 (Geocode specific)
- Variables selection heuristic specific for Geocode: dom_w_deg, restarting (luby) with random values selection heuristic, LNS