import argparse
import json
import os
import re
import subprocess
import sys

from utils import INSTANCES, MINIZINC_ERRORS, MINIZINC_MODELS, GECODE_MODELS, CHUFFED_ROTATION_MODELS
from utils import create_output_file, parse_instance_txt


# python scripts\execute_cp.py model_1 ins-13
def main() -> None:
    parser = argparse.ArgumentParser(description='Script for executing a VLSI CP model.')

    parser.add_argument('model', metavar='model', type=str, choices=MINIZINC_MODELS+[f'model_final{i}' for i in range(2)], 
                        help='The model to execute.')

    parser.add_argument('instance', metavar='instance', type=str, choices=INSTANCES, 
                    help='The instance to solve.')

    parser.add_argument('--output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('--output-name', type=str, default=None, nargs='?', 
                        help='The name of the output solution.')

    parser.add_argument('--time-limit', '-t', type=int, default=300, nargs='?',
                        help='Time limit, in seconds', required=False)

    parser.add_argument('--no-create-output', action='store_true', 
                        help='Skip the creation of the output solution.')

    parser.add_argument('--no-visualize-output', action='store_true', 
                        help='Skip the visualization of the output solution (defaults as true if --no-create-output ' + \
                        'is passed).')

    arguments = parser.parse_args()

    model = vars(arguments)['model']
    instance = vars(arguments)['instance']
    time_limit = arguments.time_limit
    
    # Open instance file
    instance_path = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(__file__))), f'instances/{instance}.txt')
    with open(instance_path,'r') as f:
        w, n, dims = parse_instance_txt(f)

    parsed_cmdline_data = _create_cmdline_data(w, n, dims)
    model_file_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), 
                                   f'cp/{"rotation_" if model in CHUFFED_ROTATION_MODELS else ""}models/{model}.mzn')
    
    if model in GECODE_MODELS:
        solver = 'solver_0'
    else:
        solver = 'solver_1'
    solver_file_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), f'cp/solvers/{solver}.mpc')
    
    command = f'minizinc {model_file_path} {parsed_cmdline_data} --time-limit {time_limit*1_000}' +\
        f'--param-file {solver_file_path}'
    
    try:
        result = subprocess.run(command, capture_output=True)
    except KeyboardInterrupt:
        # Send `UNKNOWN` error if MiniZinc returns a `KeyboardInterrupt` signal. This is due to an internal MiniZinc bug.
        sys.exit('error = UNKNOWN')
    
    try: 
        result.check_returncode()
    except subprocess.CalledProcessError:
        sys.exit(f'error = {result.stderr.decode("UTF-8")}')

    # TODO: this part of printing the output JSON is repeated ieven in solve_vlsi_cp.py
    output = result.stdout.decode('UTF-8').replace('-', '').replace('=', '')
    
    try:
        json_substring = output.split('%')[0]
        json_result = json.loads(json_substring)
        print(json_result)
    except ValueError:
        errors_re = re.compile('|'.join(MINIZINC_ERRORS))
        error_list = re.findall(errors_re, output)
        sys.exit(f'error = {error_list[0] if len(error_list) else "UNKNOWN"}')
    
    # TODO: Make this function general even for "compare_cp_models.py"
    # Print on stdout a notice that the time limit has exceeded if expressed in the result of the process.
    if '% Time limit exceeded!' in output:
        print('time = exceeded')
    # Print on stdout the last elapsed time if the information is available.
    else:
        time_list = re.findall('% time elapsed: ' + r'\d+\.\d+', output)
        if len(time_list):
            elapsed_time = time_list[-1].split('% time elapsed: ')[-1]
            if float(elapsed_time) > time_limit:
                print('time = exceeded')
            else:
                print(f'time = {elapsed_time}')

    if not arguments.no_create_output:
        l = json_result['l']
        coordsX = json_result['coordsX']
        coordsY = json_result['coordsY']
        if model in CHUFFED_ROTATION_MODELS:
            dimsX = json_result['actualDimsX']
            dimsY = json_result['actualDimsY']
            dims = list(zip(dimsX, dimsY))

        output_folder_path = arguments.output_folder_path

        output_name = arguments.output_name
        if output_name is None:
            output_file = os.path.join(output_folder_path, f'solution-{instance}.txt')
        else:
            output_file = os.path.join(output_folder_path, f'{output_name}.txt')

        try:
            create_output_file(output_file, w, n, dims, l, coordsX, coordsY)
        except FileNotFoundError:
            sys.exit(f'Output path {output_folder_path} does not exist.')
    
        if not arguments.no_visualize_output:
            scripts_folder = os.path.dirname(__file__)
            visualize_script_path = os.path.join(scripts_folder,'visualize.py')
            os.system(f'python "{visualize_script_path}" "{output_file}"')

def _create_cmdline_data(w, n, dims):
    """Create command line data string containing the parameters that are going to be given to the MiniZinc model.

    Parameters
    ----------
    w : int
        The width of the plate
    n : int
        The number of circuits
    dims : list of tuple of int
        Dims X and Y (i.e. width and height) of the circuits
    
    Returns
    -------
    command_line_string: str
        Command line data string containing the parameters that are going to be given to the MiniZinc model

    """
    # Format `dims` as a MiniZinc 2-dimensional array
    formatted_dims = f'[|{"|".join([",".join(d) for d in dims])}|]'
    
    PREFIX = '--cmdline-data'
    parsed_w = f'{PREFIX} "w = {w}"'
    parsed_n = f'{PREFIX} "n = {n}"'
    parsed_dims = f'{PREFIX} "dims = {formatted_dims}"'
    
    command_line_string = f'{parsed_w} {parsed_n} {parsed_dims}'

    return command_line_string

if __name__ == '__main__':
    main()
