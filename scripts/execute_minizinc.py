import argparse
import json
import os
import subprocess
import sys

import utils


#python scripts\execute_minizinc.py minizinc\model_1.mzn minizinc\instances\ins-13.txt minizinc\solver_0.mpc
def main() -> None:
    parser = argparse.ArgumentParser(description='Script for executing a VLSI MiniZinc model.')

    parser.add_argument('model-path', type=str, help='The model to execute.')

    parser.add_argument('instance-path', type=argparse.FileType('r', encoding='UTF-8'), help='The instance to solve.')

    parser.add_argument('solver-path', type=str, help='The solver used for optimization.')

    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('--no-create-output', action='store_true', 
                        help='Skip the creation of the output solution.')

    parser.add_argument('--no-visualize-output', action='store_true', 
                        help='Skip the visualization of the output solution (defaults as true if --no-create-output ' + \
                        'is passed).')

    arguments = parser.parse_args()

    instance_file = vars(arguments)['instance-path']
    w, n, dims = utils.parse_instance_txt(instance_file)

    parsed_cmdline_data = _create_cmdline_data(w, n, dims)

    command = f'minizinc {vars(arguments)["model-path"]} {parsed_cmdline_data} --param-file {vars(arguments)["solver-path"]}'
    result = subprocess.run(command, stdout=subprocess.PIPE)
    output = result.stdout.decode('UTF-8').replace('-', '').replace('=', '')
    time = output.split('%')[-1]
    output = output.split('%')[0]
    print(time)
    
    try:
        json_result = json.loads(output)
        print(json_result)
    except ValueError:
        sys.exit(f'Warning:\n{output}')

    if not arguments.no_create_output:
        l = json_result['l']
        coordsX = json_result['coordsX']
        coordsY = json_result['coordsY']

        output_folder_path = vars(arguments)['output-folder-path']

        instance_file_name = os.path.basename(instance_file.name)
        output_file = os.path.join(output_folder_path,f'solution-{instance_file_name}')

        try:
            utils.create_output_file(output_file, w, n, dims, l, coordsX, coordsY)
        except FileNotFoundError:
            sys.exit(f'Output path {output_folder_path} does not exist.')
    
        if not arguments.no_visualize_output:
            scripts_folder = os.path.dirname(__file__)
            visualize_script_path = os.path.join(scripts_folder,'visualize.py')
            os.system(f'python {visualize_script_path} "{output_file}"')

def _create_cmdline_data(w, n, dims):
    # Format `dims` as a MiniZinc 2-dimensional array
    formatted_dims = f'[|{"|".join([",".join(d) for d in dims])}|]'
    
    PREFIX = '--cmdline-data'
    parsed_w = f'{PREFIX} "w = {w}"'
    parsed_n = f'{PREFIX} "n = {n}"'
    parsed_dims = f'{PREFIX} "dims = {formatted_dims}"'
    
    return f'{parsed_w} {parsed_n} {parsed_dims}'

if __name__ == '__main__':
    main()
