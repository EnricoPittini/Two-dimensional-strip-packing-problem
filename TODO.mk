# Python script TODOs
- Already existing output file handling
- Check and clean visualization script

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