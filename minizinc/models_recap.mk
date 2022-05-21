# Model 0
- Lower bound of the length `l`: l_min = max([h_max, A_tot div w])
- Upper bound of the length `l`: l_max = sum(dimsY)
- Non-overlapping constraint: hand-written forall constraint (quite ineficcient)
- Non-exceeding width of the plate: hand-written forall constraint
- Definition of `l` constraint: maximum height reached

# Model 1
- **New global constraint**: Cumulative constraint `cumulative(coordsX, dimsX, dimsY, l)`
- **New global constraint**: Cumulative constraint `cumulative(coordsY, dimsY, dimsX, w)`
- Now the constraints "Non-exceeding width of the plate" and "Definition of `l` constraint" are **implied constraints**

# Model 2
- Upper bound of each `coordsY`: `l_max`
- **New global constraint**: diffn constraint `diffn(coordsX, coordsY, dimsX, dimsY)`
- Removed the "Non-overlapping constraint"

# Model 3
New variables selection heuristic 
- 3A. Variables selection heuristic based on: the rectangles areas; it interleaves coordX and coordY.
- 3B. Variables selection heuristic based on: the rectangles width; it interleaves coordX and coordY.
- 3C. Variables selection heuristic: first the coordsX, then the coordsY; the coordsX are sorted by rectangles width, the 
coordsX are sorted by rectangles height.

# Model 4
- Variables selection heuristic specific for Geocode: dom_w_deg, restarting (luby) with random values selection heuristic, LNS