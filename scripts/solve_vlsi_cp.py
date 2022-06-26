import argparse
import os
import re
import subprocess
import sys
import tempfile
from shutil import copyfile
from typing import List

from utils import INSTANCES, MINIZINC_ERRORS, parse_output_file

# MODEL_LIST = [f'model_final_{i}' for i in range(3)]
_MODEL_LIST = [f'model_final{i}' for i in range(3)]

def main() -> None:
    parser = argparse.ArgumentParser(description='Script for solving a VLSI problem with Minizinc.')

    parser.add_argument('instance', metavar='ins-1..ins-40; ins-unsat', type=str, choices=INSTANCES, 
                help='The instance to solve.')
    
    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('output-name', type=str, default=None, nargs='?', help='The name of the output solution.')

    parser.add_argument('--no-create-output', action='store_true', help='Skip the creation of the output solution.')

    parser.add_argument('--no-visualize-output', action='store_true', 
                        help='Skip the visualization of the output solution (defaults as true if --no-create-output ' + \
                        'is passed).')
    
    arguments = parser.parse_args()
    
    instance = vars(arguments)['instance']

    output_folder_path = vars(arguments)['output-folder-path']

    output_name = vars(arguments)['output-name']

    outputs = []
    errors = []
    l_results = []

    with tempfile.TemporaryDirectory() as tmp_dir_path:
        # Run the models on the instance
        _run_models(instance, tmp_dir_path, outputs, errors, l_results)
        
        if all(l is None for l in l_results):
            if len(errors) and 'UNSATISFIABLE' in errors:
                sys.exit('error = UNSATISFIABLE')
            else:
                sys.exit('error = UNKOWN')
        else:
            if output_name is None:
                output_file = os.path.join(output_folder_path, f'solution-{instance}.txt')
            else:
                output_file = os.path.join(output_folder_path, f'{output_name}.txt')
            
            best_l_result_index = l_results.index(min([float('inf') if l is None else l for l in l_results ])) 
            
            # Print the results
            _print_json_result_and_elapsed_time(outputs, best_l_result_index)
            
            best_model = _MODEL_LIST[best_l_result_index]
            
            if not arguments.no_create_output:
                copyfile(os.path.join(tmp_dir_path, f'{best_model}.txt'), output_file)
            
                # Visualize output if expressed.
                if not arguments.no_visualize_output:
                    scripts_folder = os.path.dirname(__file__)
                    visualize_script_path = os.path.join(scripts_folder,'visualize.py')
                    os.system(f'python {visualize_script_path} "{output_file}"')

def _run_models(instance: str, tmp_dir_path: str, outputs: List[str], errors: List[str], 
                l_results: List[str]) -> None:
    ''' Function that runs the models specified in `_MODEL_LIST` and saves the eventual output result files in the temporary
    directory `tmp_dir_path`. It also saves the eventual output results, the eventual errors and the eventual results of the 
    obtained lengths of the plate `l` for each execution.
    
    Parameters
    ----------
    instance : str
        String expressing the instance to solve.
    tmp_dir_path : str
        String expressing the path of the temporary directory where the output files are saved.
    outputs : list of str
        List of strings containing the otputed results of the executions of each model.
    errors : list of str
        List of strings containing the otputed errors of the executions of each model.
    l_results : list of str
        List of strings containing the results of the lenghts of the plate `l` obtained by the executions of each model.
    '''
    
    execute_minizinc_script_path = os.path.join(os.path.dirname(__file__), 'execute_minizinc.py')
    
    for model in _MODEL_LIST:
        print(f'Executing model {model}...')
        # Create the command to execute the current MiniZinc model on the instance. 
        command = f'python "{execute_minizinc_script_path}" {model} {instance} ' +\
                f'"{tmp_dir_path}" {model} --time-limit 100 --no-visualize-output'
        
        # Run the process launched by the command and save the results.
        try:
            result = subprocess.run(command, capture_output=True)
        except KeyboardInterrupt:
            # Save `UNKNOWN` error if MiniZinc returns a `KeyboardInterrupt` signal. This is due to an internal MiniZinc bug.
            outputs.append(None)
            l_results.append(None)
            errors.append('UNKNOWN')
            # Continue to the next iteration
            continue
        
        try:
            result.check_returncode()
            decoded_result = result.stdout.decode('UTF-8')
            
            outputs.append(decoded_result)
            
            # Obtain the result of `l` by the file generated by the execution of the model and append it to `l_results`.
            try:
                _, l, _, _, _, _ = parse_output_file(os.path.join(tmp_dir_path, f'{model}.txt'))
                l_results.append(l)
            # Append None to `l_results` to flag a lack of result if the output file doesn't exist.
            except OSError:
                l_results.append(None)
            
            # If an optimal solution is found exit from the loop.
            if 'time = exceeded' not in decoded_result and len(re.findall('time =', decoded_result)):
                break   
             
        except subprocess.CalledProcessError:
            # Find all errors that correspond to possible MiniZinc raised errors.
            decoded_error = result.stderr.decode('UTF-8')
            error_list = [err for err in decoded_error.split() if err in MINIZINC_ERRORS]
            
            # Print the first found MiniZinc error if it exist, otherwise print a general "UNKNOWN" error
            if len(error_list):
                errors.append(error_list[0])
            else:
                errors.append('UNKNOWN')
            
            # Append None to `outputs` and `l_results` to flag a lack of result.
            outputs.append(None)
            l_results.append(None)

def _print_json_result_and_elapsed_time(outputs: List[str], best_l_result_index: int) -> None:
    ''' Function that prints the best result obtained by the execution of the models as a json and the total elapsed time.
    
    Parameters
    ----------
    outputs : list of str
        List of strings containing the otputed results of the executions of each model.
    best_l_result_index : int
        The index of the best execution of the models.
    '''

    best_output = outputs[best_l_result_index]
    
    # Print JSON output substring of the best result of `l`.
    json_substring = best_output.split('time = ')[0]
    print(json_substring)
    
    # Print on stdout that the time limit is exceeded if that is the case.
    if 'time = exceeded' in best_output:
        print('time = exceeded')
    
    # Print on stdout the summed elapsed time if the information is available.
    else:
        total_time = 0
        for o in outputs:
            if o is None:
                time_list = []
            else:
                # Find all strings specifying the elapsed time of the current task
                time_list = re.findall('time = ' + r'\d+\.\d+', o)
            if len(time_list):
                # Add to total time the last elapsed time of the current task
                elapsed_time = time_list[-1].split('time = ')[-1]
                total_time += float(elapsed_time)
            else:
                # Add to total time maximum possible time
                total_time += 100
        print(f'time = {total_time}')

if __name__ == '__main__':
    main()
