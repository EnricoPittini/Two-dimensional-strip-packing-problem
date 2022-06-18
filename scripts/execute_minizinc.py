import argparse
import json
import os
import re
import subprocess
import sys

import utils


#python scripts\execute_minizinc.py minizinc\model_1.mzn instances\ins-13.txt minizinc\solver_0.mpc
def main() -> None:
    parser = argparse.ArgumentParser(description='Script for executing a VLSI MiniZinc model.')

    parser.add_argument('model-path', type=str, help='The model to execute.')

    parser.add_argument('instance-path', type=argparse.FileType('r', encoding='UTF-8'), help='The instance to solve.')

    parser.add_argument('solver-path', type=str, help='The solver used for optimization.')

    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('output-name', type=str, default=None, nargs='?', 
                        help='The name of the output solution.')

    parser.add_argument('--time-limit', '-t', type=int, default=300, nargs='?',
                        help='The allowed time to solve the task.', required=False)

    parser.add_argument('--no-create-output', action='store_true', 
                        help='Skip the creation of the output solution.')

    parser.add_argument('--no-visualize-output', action='store_true', 
                        help='Skip the visualization of the output solution (defaults as true if --no-create-output ' + \
                        'is passed).')
    
    #parser.add_argument('--symmetry-breaking-option', '-sbo', nargs='?',  type=int,
    #                    help='The symmetry breaking options to use for the MiniZinc model.', default=None)

    arguments = parser.parse_args()

    instance_file = vars(arguments)['instance-path']
    w, n, dims = utils.parse_instance_txt(instance_file)

    parsed_cmdline_data = _create_cmdline_data(w, n, dims)
    
    time_limit = arguments.time_limit

    command = f'minizinc {vars(arguments)["model-path"]} {parsed_cmdline_data} --param-file {vars(arguments)["solver-path"]}'
    
    try:
        result = subprocess.run(command, capture_output=True)
    except KeyboardInterrupt:
        # Send `UNKNOWN` error if MiniZinc returns a `KeyboardInterrupt` signal. This is due to an internal MiniZinc bug.
        sys.exit('ERROR: UNKNOWN')
    
    try: 
        result.check_returncode()
    except subprocess.CalledProcessError:
        sys.exit(f'ERROR: {result.stderr.decode("UTF-8")}')

    # TODO: this part of printing the output JSON is repeated ieven in solve_vlsi_cp.py
    output = result.stdout.decode('UTF-8').replace('-', '').replace('=', '')
    
    try:
        json_substring = output.split('%')[0]
        json_result = json.loads(json_substring)
        print(json_result)
    except ValueError:
        errors_re = re.compile('|'.join(utils.MINIZINC_ERRORS))
        error_list = re.findall(errors_re, output)
        sys.exit(f'ERROR: {error_list[0] if len(error_list) else "UNKNOWN"}')
    
    # TODO: Make this function general even for "compare_minizinc_models.py"
    # Print on stdout a notice that the time limit has exceeded if expressed in the result of the process.
    if '% Time limit exceeded!' in output:
        print('% Time limit exceeded!')
    # Print on stdout the last elapsed time if the information is available.
    else:
        time_list = re.findall('% time elapsed: ' + r'\d+\.\d+', output)
        if len(time_list):
            elapsed_time = time_list[-1].split('% time elapsed: ')[-1]
            if float(elapsed_time) > time_limit:
                print('% Time limit exceeded!')
            else:
                print(time_list[-1])

    if not arguments.no_create_output:
        l = json_result['l']
        coordsX = json_result['coordsX']
        coordsY = json_result['coordsY']

        output_folder_path = vars(arguments)['output-folder-path']

        instance_file_name = os.path.basename(instance_file.name)
        output_name = vars(arguments)['output-name']
        if output_name is None:
            output_file = os.path.join(output_folder_path, f'solution-{instance_file_name}')
        else:
            output_file = os.path.join(output_folder_path, f'{output_name}.txt')

        try:
            utils.create_output_file(output_file, w, n, dims, l, coordsX, coordsY)
        except FileNotFoundError:
            sys.exit(f'Output path {output_folder_path} does not exist.')
    
        if not arguments.no_visualize_output:
            scripts_folder = os.path.dirname(__file__)
            visualize_script_path = os.path.join(scripts_folder,'visualize.py')
            os.system(f'python "{visualize_script_path}" "{output_file}"')

def _create_cmdline_data(w, n, dims):
    # Format `dims` as a MiniZinc 2-dimensional array
    formatted_dims = f'[|{"|".join([",".join(d) for d in dims])}|]'
    
    PREFIX = '--cmdline-data'
    parsed_w = f'{PREFIX} "w = {w}"'
    parsed_n = f'{PREFIX} "n = {n}"'
    parsed_dims = f'{PREFIX} "dims = {formatted_dims}"'
    
    command_line_string = f'{parsed_w} {parsed_n} {parsed_dims}'
    
    # symmetry_breaking_option = arguments.symmetry_breaking_option
    #if symmetry_breaking_option is not None:
    #    command_line_string += f' {PREFIX} "symmetry_breaking_option = {symmetry_breaking_option}"'
    
    return command_line_string

if __name__ == '__main__':
    main()
