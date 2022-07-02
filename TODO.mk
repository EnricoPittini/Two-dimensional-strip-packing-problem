# Python script TODOs
- Static types refactoring
- Try-except handling
- Already existing output file handling
- Check and clean visualization script
- Handle platform path independency
- Solver parameters through script
- Automatic instance and model path files retrival
- Delete time selection from solver config and put it directly in minizinc call in execute_minizinc.py

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
- Delete instance 41
- Fix name exactly_one for coords (name=f'exactly_one_coord_{k}')

- Try refactor and use timeout of the Z3 solver (instead of using a Thread)
- Refactor the different Vlsi_sat classes
- Add better bounds (e.g. w-w_min) to the encodings 10

- Refactor execute_sat compare_sat_encodings
- Refactor results folder (also smt)
- Binary search: ub and lb with -1, compute th best l (do not take the med l_med)