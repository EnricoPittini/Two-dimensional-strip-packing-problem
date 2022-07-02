import multiprocessing

class Vlsi_smt_abstract(multiprocessing.Process):
    """Class for solving the VLSI problem using SMT.

    It inheriths from `multiprocessing.Process`, in order to be executable as parallel process.
    The typical usage is to run this process in parallel using a certain time limit. In such case, if the time limit exceeds,
    the user is not guaranteed to get an optimal solution, but only the best solution found so far.

    It is a general class, it is not a specific encoding.
    It collects the basic common attributes and properties, shared among the different SMT encodings. 
    A SMT encoding class inherits from this class.

    Attributes
    ----------
    instance_name : str
        Name of the instance to solve (e.g. 'ins-1')
    solver_name : str
        Name of the solver (e.g. 'z3')
    time_limit : int
        Time limit, in seconds.
    w : int
        The width of the plate
    n : int
        The number of circuits
    dimsX : list of int
        Dims X (i.e. width) of the circuits
    dimsY : list of int
        Dims Y (i.e. height) of the circuits
    results : dict
        Dictionary containing the results. It contains three elements.
            1. results['best_coords'] : list of tuples of int
               List containing the coordX and coordY of the lower-left vertex of each circuit in the best solution.
            2. results['best_l'] : int
               Length of the plate in the best solution.
            3. results['finish'] : bool
               Boolean flag saying whether the solving has finished or not.
               (This is useful in particular if this class is run as parallel process with a time limit).
            4. results['unsat'] : bool
               Boolean flag saying whether the problem is UNSAT or not.
               (For proving that the problem is UNSAT, the solving process must have finishe, therefore results['finish'] 
               must be True).
    
    Notes
    -----
    The way the user and the `Vlsi_smt` class instance communicate is through the `results` dictionary. It is given to the
    class constructor and it is stored inside the class: then, it is modified by injecting the solution (this each time a 
    better solution is found).

    """

    def __init__(self, instance_name, solver_name, time_limit, w, n, dims, results):
        super().__init__()

        self.instance_name = instance_name
        self.solver_name = solver_name
        self.time_limit = time_limit
        self.w = w
        self.n = n 
        self.dimsX = [dims[i][0] for i in range(n)]
        self.dimsY = [dims[i][1] for i in range(n)]

        self.results = results
        self.results['best_coords'] = None
        self.results['best_l'] = None
        self.results['finish'] = False
        self.results['unsat'] = False