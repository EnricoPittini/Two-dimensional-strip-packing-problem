# Python script TODOs
- Static types refactoring
- Try-except handling
- Already existing output file handling
- Check and clean visualization script
- Handle platform path independency
- Solver parameters through script
- Automatic instance and model path files retrival

# MiniZinc model TODOs
- Heuristic
- Remove 'dims' and keep only 'dimsX, dimsY'
- Set refactoring
- For the final model try Graph vs Bound consistency
- Test "gecode" (restarting "dom_w_deg" "LNS")

# Generic TODOs
- Possible solve perfect model

# SAT TODOs
- Fix in-file TODOs 
- Refactor and write better encoding 3, in order to fix it (write functions to access the indeces of the length_k_l variables)
- Think about the constraints. In particular, think about the equivalence, about the implications, about the 'redundant' constraints
- Sliding window constraints
- Implement encoding found in the pdf
- Try binary search for optimization
- Try other encodings of at most one (see the paper)
- Put simmetry breaking constraints
- Add timeout info (timeout/not timeout)
- Improve timeout
- Put the 'run()' method in the superclass
- Delete instance 41
- Fix bounds of the variables in the comments (e.g. w-w_min)
- Fix name exactly_one for coords (name=f'exactly_one_coord_{k}')

- Try refactor and use timeout of the Z3 solver (instead of using a Thread)
- Refactor the different Vlsi_sat classes
- Add better bounds (e.g. w-w_min) to the encodings 10