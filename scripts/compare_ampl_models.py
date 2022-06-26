import argparse
import json
import os
import re
import subprocess
from scripts.utils import AMPL_SOLVER_CHOICES

from utils import AMPL_MODEL_CHOICES


# SOLVER_CHOICES = [f'solver_{i}' for i in range(3)]
#python scripts/compare_minizinc_models.py minizinc instances minizinc\solver_1.mpc results/ --models-list model_2 model_3A model_3B model_3C -lb 1 -ub 8
def main() -> None:
    parser = argparse.ArgumentParser(description='Script comparing the execution time of MiniZinc models on a VLSI problem.')

    parser.add_argument('output-folder-path', type=str, 
                        default=os.path.dirname(os.path.dirname(__file__), 'results/lp'), nargs='?', 
                        help='The path in which the output file is stored.')
    
    parser.add_argument('output-name', type=str, default='solution', nargs='?', 
                        help='The name of the output solution.')

    parser.add_argument('--models-list', '-m',
                        metavar='model',
                        type=str, 
                        choices=AMPL_MODEL_CHOICES,
                        default=AMPL_MODEL_CHOICES,
                        # TODO: correct description
                        help='List of models to compare (default all models). ' +\
                        'Example of usage: --models-list model_0 model_2 model_3',
                        nargs='*')
    
    parser.add_argument('--solvers-list', '-m',
                    metavar='solver',
                    type=str, 
                    choices=AMPL_SOLVER_CHOICES,
                    default=AMPL_SOLVER_CHOICES,
                    help='List of solvers to use for comparison (default all solvers). ' +\
                    'Example of usage: --solvers-list cplex cbc gurobi',
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

    arguments = parser.parse_args()
    
    output_folder_path = vars(arguments)['output-folder-path']
    output_file_name = vars(arguments)['output-name']
    output_file = os.path.join(output_folder_path, f'{output_file_name}.json')
    os.makedirs(os.path.dirname(output_folder_path), exist_ok=True)
    
    models_list = arguments.models_list
    
    solvers_list = arguments.solvers_list
    
    instances_lower_bound = arguments.instances_lower_bound
    instances_upper_bound = arguments.instances_upper_bound
    if instances_lower_bound > instances_upper_bound:
        parser.error(f'argument --instances-lower-bound/-lb: invalid choice: {instances_lower_bound} ' 
                     f'(must be lower or equal than --instances-upper-bound/-ub: {instances_upper_bound})')
    instances_range = range(instances_lower_bound, instances_upper_bound + 1) 
    
    execute_ampl_script_path = os.path.join(os.path.dirname(__file__), 'execute_ampl.py')

    result_list = []

    # TODO: handling of error solutions
    for instance in instances_range:
        instance_dict = dict()
        for model in models_list:
            for solver in solvers_list:
                print(f'Executing instance {instance} with model {model} with solver {solver}...')
                
                command = f'python "{execute_ampl_script_path}" {model} {instance} {solver} --no-create-output'
                
                result = subprocess.run(command, capture_output=True)
                
                try:
                    result.check_returncode()
                except subprocess.CalledProcessError:
                    stderror = result.stderr.decode('UTF-8')
                    error_list = re.findall('error = ' + r'(UNSATISFIABLE|UNKNOWN)', stderror)
                    if len(error_list):
                        error = error_list[0].split("= ")[-1]
                        print(f'\tERROR: {error}')
                        instance_dict[f'{model}_{solver}'] = error
                    else:
                        print('\tERROR: UNKNOWN')
                        instance_dict[f'{model}_{solver}'] = 'UNKNOWN'
                    # Continue to the next iteration.
                    continue
            
                stdout = result.stdout.decode('UTF-8')
                time_list = re.findall('time = ' + r'\d+\.\d+', stdout)
                if len(time_list):
                    elapsed_time = time_list[-1].split('= ')[-1]
                    print(f'\tsolved in {elapsed_time}s.')
                    instance_dict[f'{model}_{solver}'] = float(elapsed_time)
                elif 'time = exceeded' in stdout:
                    print('\tTime limit exceeded.')
                    l_list = re.findall('l = ' + r'\d', stdout)
                    if len(time_list):
                        l = l_list[-1].split('= ')[-1]
                        instance_dict[f'{model}_{solver}'] = f'NaN; l = {l}'
                    else:
                        instance_dict[f'{model}_{solver}'] = 'NaN'
                else: 
                    print('\tERROR: UNKNOWN.')
                    instance_dict[f'{model}_{solver}'] = 'UNKNOWN'
                    
            result_list.append({f'ins-{instance}': instance_dict})

        # Save intermediate JSON solution.
        with open(output_file, 'w') as f:
            json.dump(result_list, f, sort_keys=False, indent=4, separators=(',', ': '))

if __name__ == '__main__':
    main()
