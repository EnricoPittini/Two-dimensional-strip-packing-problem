import argparse
import multiprocessing
import sys
import os

import importlib

import time

import utils
#python scripts\execute_sat.py sat\encoding_2.py instances\ins-10.txt 300


def vlsi_sat(w, n, dims, encoding_module, timeout=300):
    """Solves the given VLSI instance, using the specified SAT encoding

    It runs the solving process in parallel, within the specified time limit.

    The encoding is specified by giving the Python module object containing it.
    In particular, this module contains the class `Vlsi_sat`, which solves the problem with a certain encoding.

    Parameters
    ----------
    w : int
        The width of the plate
    n : int
        The number of circuits
    dims : list of tuple of int
        Dims X and Y (i.e. width and height) of the circuits
    encoding_module : module
        Python module object containing the specified SAT encoding.
        (The encoding is contained in the `Vlsi_sat` class)
    timeout : int, optional.
        Time limit in seconds for executing the SAT solver, by default 300 (i.e. 5 minutes)

    Returns
    -------
    best_coords: list of tuples of int
        List containing the coordX and coordY of the lower-left vertex of each circuit in the best solution
    best_l: int
        Length of the plate in the best solution
    finish: bool
        Boolean flag saying whether the solving has finished or not.
        (This is useful in particular for understanding whether the time has elapsed or not)

    Raises
    ------
    UnsatError
        If the given instance is UNSAT.

    Raises
    ------
    The communication with the `Vlsi_sat` class instance is done through the `results` dictionary. It is given to the
    class constructor and it is stored inside the class: then, it is modified by injecting the solution (this each time a 
    better solution is found).
    Indeed, this dictionary contains the keys 'best_coords', 'best_l', 'finish'.
    """
    manager = multiprocessing.Manager()
    results = manager.dict()
    p = encoding_module.Vlsi_sat(w, n, dims, results)
    p.start()

    p.join(timeout)

    if p.is_alive():
        p.terminate()
        p.join()   

    return results['best_coords'], results['best_l'], results['finish']
      

def main():
    parser = argparse.ArgumentParser(description='Script for executing a VLSI SAT encoding.')

    parser.add_argument('encoding-path', type=str, help='The encoding to execute.')

    parser.add_argument('instance-path', type=argparse.FileType('r', encoding='UTF-8'), help='The instance to solve.')

    parser.add_argument('time-limit', type=int, default=300, nargs='?', help='Time limit, in seconds')

    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('--no-create-output', action='store_true', 
                        help='Skip the creation of the output solution.')

    parser.add_argument('--no-visualize-output', action='store_true', 
                        help='Skip the visualization of the output solution (defaults as true if `--no-create-output` ' + \
                        'is passed).')

    arguments = parser.parse_args()

    instance_file = vars(arguments)['instance-path']
    w, n, dims = utils.parse_instance_txt(instance_file)
    w = int(w)
    n = int(n)
    dims = [(int(dims[i][0]),int(dims[i][1])) for i in range(n)]

    encoding_path = vars(arguments)['encoding-path']
    encoding_abspath = os.path.abspath(encoding_path)
    module_name = os.path.basename(encoding_path).split('.')[0]
    sys.path.insert(1, os.path.join(os.path.dirname(__file__), os.path.dirname(encoding_abspath)))
    encoding_module = importlib.import_module(module_name)
    # vlsi_sat = encoding_module.vlsi_sat
    UnsatError = encoding_module.UnsatError  # TODO refactor

    try:
        start_time = time.time()
        coords, l, finish = vlsi_sat(w, n, dims, encoding_module=encoding_module, timeout=vars(arguments)['time-limit'])        
        solving_time = time.time() - start_time

        if not finish:  # Time out
            print('Time elapsed')

        print('Time:', solving_time)

        if not coords:  # The time is elapsed and no solution has been found: UNSAT. (It is UNSAT within the time limit).
                        # No solution
            raise UnsatError()

        # We have at least a solution.
        # (It is guaranteed to be the best one iff the time is not elapsed).
        coordsX = [coords[i][0] for i in range(n)]
        coordsY = [coords[i][1] for i in range(n)]

    except UnsatError:
        sys.exit('UNSAT')

    if not arguments.no_create_output:
        output_folder_path = vars(arguments)['output-folder-path']

        instance_file_name = os.path.basename(instance_file.name)
        output_file = os.path.join(output_folder_path,f'solution-{instance_file_name}')#f'{output_folder_path}\\solution-{instance_file.name.split("/")[-1]}'

        try:
            utils.create_output_file(output_file, w, n, dims, l, coordsX, coordsY)
        except FileNotFoundError as e:
            #print(e) 
            sys.exit(f'Output path {output_folder_path} does not exist.')
    
        if not arguments.no_visualize_output:
            scripts_folder = os.path.dirname(sys.argv[0])
            visualize_script_path = os.path.join(scripts_folder,'visualize.py')
            print(output_file)
            os.system(f'python {visualize_script_path} "{output_file}"')


if __name__ == "__main__":
    main()