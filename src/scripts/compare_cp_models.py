import argparse
import json
import os
import re
import subprocess

from utils import MINIZINC_MODELS, MINIZINC_ERRORS


# python src/scripts/compare_cp_models.py --models-list model_2 model_3A model_3B model_3C -lb 1 -ub 8
def main() -> None:
    parser = argparse.ArgumentParser(description='Script comparing the execution time of MiniZinc models on a VLSI problem.')

    parser.add_argument('output-name', type=str, default='results', nargs='?', 
                help='The name of the output solution.')

    parser.add_argument('output-folder-path', type=str, 
                        default=os.path.normpath('results/cp/'), 
                        nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('--models-list', '-m',
                        metavar='model',
                        type=str, 
                        choices=MINIZINC_MODELS,
                        default=['model_6D1'],
                        help='List of models to compare (default all models). ' +\
                        'Example of usage: --models-list model_0 model_2 model_3',
                        nargs='*')

    parser.add_argument('--instances-lower-bound', '-lb',
                        metavar='1..40',
                        type=int,
                        choices=range(1, 41),
                        default=1,
                        help='Lower bound of instances to solve (default 1).',
                        nargs='?')

    parser.add_argument('--instances-upper-bound', '-ub', 
                        metavar='1..40',
                        type=int,
                        choices=range(1, 41),
                        default=40,
                        help='Upper bound of instances to solve (default 40).', 
                        nargs='?')
    
    parser.add_argument('--no-visualize', action='store_true', help='Do not visualize the obtained comparisons.')

    arguments = parser.parse_args()
    
    output_folder_path = vars(arguments)['output-folder-path']
    output_file_name = vars(arguments)['output-name']
    output_file = os.path.join(output_folder_path, f'{output_file_name}.json')
    os.makedirs(output_folder_path, exist_ok=True)
    
    models_list = arguments.models_list
    
    instances_lower_bound = arguments.instances_lower_bound
    instances_upper_bound = arguments.instances_upper_bound
    if instances_lower_bound > instances_upper_bound:
        parser.error(f'argument --instances-lower-bound/-lb: invalid choice: {instances_lower_bound} ' 
                     f'(must be lower or equal than --instances-upper-bound/-ub: {instances_upper_bound})')
    instances_range = range(instances_lower_bound, instances_upper_bound + 1) 
    
    execute_cp_script_path = os.path.join(os.path.dirname(__file__), 'execute_cp.py')

    result_dict = dict()

    for instance in instances_range:
        instance_dict = dict()
        for model in models_list:
            print(f'Executing instance {instance} with model {model}...')    
            command = f'python "{execute_cp_script_path}" "{model}" "ins-{instance}" ' +\
                    '--time-limit 300 --no-create-output'

            try:
                result = subprocess.run(command, capture_output=True)
            except KeyboardInterrupt:
                # Specify `UNKNOWN` error if MiniZinc returns a `KeyboardInterrupt` signal. 
                # This is due to an internal MiniZinc bug.
                print('\tERROR: UNKNOWN')
                instance_dict[model] = 'UNKNOWN'
                # Continue to the next iteration.
                continue
            
            try:
                result.check_returncode()
            except subprocess.CalledProcessError:
                decoded_error = result.stderr.decode('UTF-8')
                error_list = [err for err in decoded_error.split() if err in MINIZINC_ERRORS]
                if len(error_list):
                    print(f'\tERROR: {error_list[0]}')
                    instance_dict[model] = error_list[0]
                else:
                    print('\tERROR: UNKNOWN')
                    instance_dict[model] = 'UNKNOWN'
                # Continue to the next iteration.
                continue
            
            stdout = result.stdout.decode('UTF-8')
            time_list = re.findall('time = ' + r'\d+\.\d+', stdout)
            if len(time_list):
                elapsed_time = time_list[-1].split('= ')[-1]
                print(f'\tSolved in {elapsed_time}s.')
                instance_dict[model] = float(elapsed_time)
            elif 'time = exceeded' in stdout:
                print('\tTime limit exceeded.')
                instance_dict[model] = 'NaN'
            else: 
                print('\tERROR: UNKNOWN.')
                instance_dict[model] = 'UNKNOWN'
                
        result_dict[f'ins-{instance}'] = instance_dict

        # Save intermediate JSON solution.
        with open(output_file, 'w') as f:
            json.dump(result_dict, f, sort_keys=False, indent=4, separators=(',', ': '))

    if not arguments.no_visualize:
        plot_comparisons_path = os.path.join(os.path.dirname(__file__), 'plot_comparisons.py')
        command = f'python "{plot_comparisons_path}" "{output_file}"'
        subprocess.run(command)

if __name__ == '__main__':
    main()
