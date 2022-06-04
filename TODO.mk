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
- Try other encodings of at most one
- Put simmetry breaking constraints
- Add timeout info (timeout/not timeout)
- Improve timeout