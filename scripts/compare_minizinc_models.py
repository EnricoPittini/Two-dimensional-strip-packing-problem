import argparse
import json
import os
import re
import subprocess


# TODO: Fix 
MODEL_CHOICES = [f'model_{i}' for i in range(3)] + [f'model_{j}{i}' for i in ['A', 'B', 'C', 'D'] for j in [3, 4]] + \
    ['model_5_gecode', 'model_6']

# SOLVER_CHOICES = [f'solver_{i}' for i in range(3)]
#python scripts/compare_minizinc_models.py minizinc minizinc/instances minizinc\solver_1.mpc results/ --models-list model_2 model_3A model_3B model_3C -lb 1 -ub 8
def main() -> None:
    parser = argparse.ArgumentParser(description='Script for executing a VLSI MiniZinc model.')

    parser.add_argument('models-folder-path', type=str, help='The folder path of the models to compare.')

    parser.add_argument('instances-folder-path', type=str, help='The folder path of the instances to solve.')

    parser.add_argument('solvers-folder-path', type=str, help='The folder path of the solvers used for optimization.')
    
    # parser.add_argument('solver-path', type=str, help='The solver used for optimization.')

    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('--models-list', '-m',
                        metavar='model',
                        type=str, 
                        #choices=MODEL_CHOICES,
                        # TODO: add all possible model choices
                        default=['model_0', 'model_1', 'model_2', 'model_3'], #'model_4_gecode'
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

    arguments = parser.parse_args()
    
    instances_folder_path = vars(arguments)['instances-folder-path']

    models_folder_path = vars(arguments)['models-folder-path']
    
    solvers_folder_path = vars(arguments)['solvers-folder-path']

    output_folder_path = vars(arguments)['output-folder-path']

    execute_minizinc_script_path = os.path.join(os.path.dirname(__file__), 'execute_minizinc.py')

    result_list = []

    models_list = arguments.models_list
    
    instances_lower_bound = arguments.instances_lower_bound
    instances_upper_bound = arguments.instances_upper_bound
    if instances_lower_bound > instances_upper_bound:
        parser.error(f'argument --instances-lower-bound/-lb: invalid choice: {instances_lower_bound} ' 
                     f'(must be lower or equal than --instances-upper-bound/-ub: {instances_upper_bound})')
    
    instances_range = range(instances_lower_bound, instances_upper_bound + 1) 

    output_file = os.path.join(output_folder_path, 'solution.json')
    os.makedirs(os.path.dirname(output_folder_path), exist_ok=True)

    # TODO: handling of error solutions
    for instance in instances_range:
        instance_file_path = os.path.join(instances_folder_path, f'ins-{instance}.txt')
        instance_dict = dict()
        for model in models_list:
            model_file_path = os.path.join(models_folder_path, f'{model}.mzn')
            if model == 'model_4D':
                solver_file_path = os.path.join(solvers_folder_path, 'solver_0.mpc')
            else:
                solver_file_path = os.path.join(solvers_folder_path, 'solver_1.mpc')


            print(f'Executing instance {instance} with model {model}...')
            command = f'python "{execute_minizinc_script_path}" "{model_file_path}" "{instance_file_path}" ' +\
                      f'"{solver_file_path}" --no-create-output'
            result = subprocess.run(command, capture_output=True)
            
            try: 
                result.check_returncode()
            except subprocess.CalledProcessError:
                print('\tUnsat')
                instance_dict[model] = 'Unsat'
                # Continue to the next iteration.
                continue
            
            output = result.stdout.decode('UTF-8')
            time_list = re.findall('% time elapsed: ' + r'\d+\.\d+', output)
            if len(time_list):
                elapsed_time = time_list[-1].split('% time elapsed: ')[-1]
                print(f'\tsolved in {elapsed_time}s.')
                instance_dict[model] = float(elapsed_time)
            elif 'Time limit exceeded!' in output:
                print('\tTime limit exceeded.')
                instance_dict[model] = 'NaN'
            else: 
                print('\tUnsat.')
                instance_dict[model] = 'Unsat'
                
        result_list.append({f'ins-{instance}': instance_dict})

        # Save intermediate JSON solution.
        with open(output_file, 'w') as f:
            json.dump(result_list, f, sort_keys=False, indent=4, separators=(',', ': '))

if __name__ == '__main__':
    main()
