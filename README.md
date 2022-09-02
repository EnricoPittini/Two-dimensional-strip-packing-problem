# :iphone: Very Large Scale Integration (VLSI) Optimization 🧩
Description here

## Repository structure

    .
    ├── images
    │   ├── cp                              # Plots of the performances of the CP models
    │   ├── lp                              # Plots of the performances of the LP models
    │   ├── sat                             # Plots of the performances of the SAT encodings
    │   └── smt                             # Plots of the performances of the SMT encodings
    ├── instances                           # Directory containing the instances to solve in `.txt` format
    ├── report
    ├── results
    │   ├── cp                              # Json results of the performances of the CP models
    │   ├── lp                              # Json results of performances of the LP models
    │   ├── sat                             # Json results of the performances of the SAT encodings
    │   └── smt                             # Json results of performances of the SMT encodings
    ├── solutions
    │   ├── cp                              # Solutions for the given instances using CP
    │   ├── cp-rotations                    # Solutions for the given instances accounting for rotations using CP
    │   ├── lp                              # Solutions for the given instances using LP
    │   ├── lp-rotations                    # Solutions for the given instances accounting for rotations using LP
    │   ├── sat                             # Solutions for the given instances using SAT
    │   ├── sat-rotations                   # Solutions for the given instances accounting for rotations using SAT
    │   ├── smt                             # Solutions for the given instances using SMT
    │   └── smt-rotations                   # Solutions for the given instances accounting for rotations using SMT
    ├── src
    │   ├── cp                      
    │   │   ├── data                        # Directory containing data examples for the problem in CP
    │   │   ├── models                      # Directory containing the models solving the problem in CP
    │   │   ├── rotation_models             # Directory containing the models solving the problem in CP considering rotations
    │   │   ├── solvers                     # Directory containing the solver configurations for CP
    │   │   └── project_cp.mzp              # MiniZinc CP project
    │   ├── lp                              # Directory containing the models solving the problem in LP
    │   ├── sat                             # Directory containing the encodings solving the problem in SAT
    │   ├── scripts                      
    │   │   ├── compare_cp_models.py        # Script to compare the results of CP models on the instances
    │   │   ├── compare_lp_models.py        # Script to compare the results of LP models on the instances
    │   │   ├── compare_sat_encodings.py    # Script to compare the results of SAT encodings on the instances
    │   │   ├── compare_smt_encodings.py    # Script to compare the results of SMT encodings on the instances
    │   │   ├── execute_cp.py               # Script to solve an instance using CP
    │   │   ├── execute_lp.py               # Script to solve an instance using LP
    │   │   ├── execute_sat.py              # Script to solve an instance using SAT
    │   │   ├── execute_smt.py              # Script to solve an instance using SMT
    │   │   ├── plot_comparisons.py         # Script to plot the results of the use of different models on the instances
    │   │   ├── position_and_covering.py    # Script applying the Position and Covering technique for LP
    │   │   ├── solve_all_instances_cp.py   # Script solving all instances with CP
    │   │   ├── solve_all_instances_lp.py   # Script solving all instances with LP
    │   │   ├── solve_all_instances_sat.py  # Script solving all instances with SAT
    │   │   ├── solve_all_instances_smt.py  # Script solving all instances with SMT
    │   │   ├── solve_all_instances.py      # Script solving all instances with a desired methodology
    │   │   ├── utils.py                    # Script containing useful functions
    │   │   └── visualize.py                # Script to visualize a solved instance
    │   └── smt                             # Directory containing the encodings solving the problem in SMT
    ├── .gitattributes
    ├── .gitignore
    ├── LICENSE
    └── README.md

## Usage

## Versioning

Git is used for versioning.

## Group members

|  Name           |  Surname  |     Email                           |    Username                                             |
| :-------------: | :-------: | :---------------------------------: | :-----------------------------------------------------: |
| Antonio         | Politano  | `antonio.politano2@studio.unibo.it` | [_S1082351_](https://github.com/S1082351)               |
| Enrico          | Pittini   | `enrico.pittini@studio.unibo.it`    | [_EnricoPittini_](https://github.com/EnricoPittini)     |
| Riccardo        | Spolaor   | `riccardo.spolaor@studio.unibo.it`  | [_RiccardoSpolaor_](https://github.com/RiccardoSpolaor) |

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
