import argparse
import json
import os
import re
import subprocess
import tempfile
from shutil import copyfile

import utils


def main() -> None:
    parser = argparse.ArgumentParser(description='Script for solving a VLSI problem with Minizinc.')

    parser.add_argument('instance-path', type=str, help='The instance to solve.')
    
    # parser.add_argument('solver-path', type=str, help='The solver used for optimization.')

    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('output-name', type=str, default=None, nargs='?', 
                        help='The name of the output solution.')

    #parser.add_argument('--no-create-output', action='store_true', 
    #                    help='Skip the creation of the output solution.')

    parser.add_argument('--no-visualize-output', action='store_true', 
                        help='Skip the visualization of the output solution.')

    arguments = parser.parse_args()
    
    instance_file_path = vars(arguments)['instance-path']

    output_folder_path = vars(arguments)['output-folder-path']

    output_name = vars(arguments)['output-name']

    execute_minizinc_script_path = os.path.join(os.path.dirname(__file__), 'execute_minizinc.py')

    solver_file_path = os.path.join(os.path.dirname(__file__), '../minizinc/solver_2.mpc')

    #result_list = []

    model_folder_path = os.path.join(os.path.dirname(__file__), '../minizinc')

    MODEL_LIST = [f'model_final_{i}.mzn' for i in range(3)]

    errors = []

    results = []

    with tempfile.TemporaryDirectory() as tmpdirname:

        for model in MODEL_LIST:
            print(f'Executing model {model}...')
            command = f'python "{execute_minizinc_script_path}" "{model}" "{instance_file_path}" ' +\
                    f'"{solver_file_path}" "{tmpdirname}" {model} --no-visualize-output'
            result = subprocess.run(command, capture_output=True)
            
            try: 
                result.check_returncode()
            except subprocess.CalledProcessError as e:
                error_list = str(e).split('ERROR: ')
                if len(error_list) and error_list[-1] in utils.MINIZINC_ERRORS:
                    errors.append(error_list[-1])
                else:
                    errors.append('UNKNOWN')

    
        for model in MODEL_LIST:
            try:
                _, l, _, _, _, _ = utils.parse_output_file(os.path.join(tempfile.tempdir,f'{model}.txt'))
                results.append(l)
            except OSError:
                results.append(None)
        # TODO Write this thing decently please
        if results is [None, None, None]:
            if len(errors) and 'UNSATISFIABLE' in errors:
                print('UNSATISFIABLE')
            else:
                print('UNKOWN')
        else:
            if output_name is None:
                output_file = os.path.join(output_folder_path, os.path.basename(instance_file_path))
            else:
                output_file = os.path.join(output_folder_path, f'{output_name}.txt')
            best_model = MODEL_LIST[results.index(min(results))]
            copyfile(os.path.join(tempfile.tempdir,f'{best_model}.txt'), output_file)
            if not arguments.no_visualize_output:
                scripts_folder = os.path.dirname(__file__)
                visualize_script_path = os.path.join(scripts_folder,'visualize.py')
                os.system(f'python {visualize_script_path} "{output_file}"')

if __name__ == '__main__':
    main()
