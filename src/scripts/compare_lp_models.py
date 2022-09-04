import argparse
import json
import os
import re
import subprocess

from utils import AMPL_SOLVER_CHOICES, AMPL_MODEL_CHOICES


#python src/scripts/compare_lp_models.py --models-list model_2 --solvers-list cplex -lb 1 -ub 10
def main() -> None:
    parser = argparse.ArgumentParser(description='Script comparing the execution time of CP models on a VLSI problem.')

    parser.add_argument('output-name', type=str, default='results', nargs='?', 
                    help='The name of the output solution.')

    parser.add_argument('output-folder-path', type=str, 
                        default=os.path.normpath('results/lp/'), 
                        nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('--models-list', '-m',
                        metavar='model',
                        type=str, 
                        choices=AMPL_MODEL_CHOICES,
                        default=AMPL_MODEL_CHOICES,
                        help='List of models to compare (default all models). ' +\
                        'Example of usage: --models-list model_0 model_1 model_2A',
                        nargs='*')
    
    parser.add_argument('--solvers-list', '-s',
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
    
    parser.add_argument('--use-symmetry', action='store_true', 
                    help='Break symmetries in the presolve process.')
    
    parser.add_argument('--use-dual', action='store_true', 
                    help='Use the dual model.')
    
    parser.add_argument('--use-no-presolve', action='store_true', 
                    help='Avoid AMPL presolving process.')

    parser.add_argument('--no-visualize', action='store_true', help='Do not visualize the obtained comparisons.')

    arguments = parser.parse_args()
    
    output_folder_path = vars(arguments)['output-folder-path']
    output_file_name = vars(arguments)['output-name']
    output_file = os.path.join(output_folder_path, f'{output_file_name}.json')
    os.makedirs(output_folder_path, exist_ok=True)
    
    models_list = arguments.models_list
    
    solvers_list = arguments.solvers_list
    
    use_symmetry = arguments.use_symmetry
    use_dual = arguments.use_dual
    use_no_presolve = arguments.use_no_presolve
    
    instances_lower_bound = arguments.instances_lower_bound
    instances_upper_bound = arguments.instances_upper_bound
    if instances_lower_bound > instances_upper_bound:
        parser.error(f'argument --instances-lower-bound/-lb: invalid choice: {instances_lower_bound} ' 
                     f'(must be lower or equal than --instances-upper-bound/-ub: {instances_upper_bound})')
    instances_range = range(instances_lower_bound, instances_upper_bound + 1) 
    
    execute_lp_script_path = os.path.join(os.path.dirname(__file__), 'execute_lp.py')

    result_dict = dict()

    for instance in instances_range:
        instance_dict = dict()
        for model in models_list:
            for solver in solvers_list:
                print(f'Executing instance {instance} with model {model} with solver {solver} ' + 
                      f'{"with symmetries" if use_symmetry else ""} ' + 
                      f'{"with dual" if use_dual else ""} ' +
                      f'{"with no presolve" if use_no_presolve else ""}...')
                
                command = f'python "{execute_lp_script_path}" {model} ins-{instance} "{solver}" --no-create-output ' +\
                    f'{"--use-symmetry" if use_symmetry else ""} {"--use-dual" if use_dual else ""} ' +\
                    f'{"--use-no-presolve" if use_no_presolve else ""}'
                
                result = subprocess.run(command, capture_output=True)
                
                model_name = f'{model}_{solver}{"_symmetry" if use_symmetry else ""}{"_dual" if use_dual else ""}' +\
                    f'{"_no_presolve" if use_no_presolve else ""}'
                
                try:
                    result.check_returncode()
                except subprocess.CalledProcessError:
                    stderror = result.stderr.decode('UTF-8')
                    error_list = re.findall('error = ' + r'(UNSATISFIABLE|UNKNOWN)', stderror)
                    if len(error_list):
                        error = error_list[0].split("= ")[-1]
                        print(f'\tERROR: {error}')
                        instance_dict[model_name] = error
                    else:
                        print('\tERROR: UNKNOWN')
                        instance_dict[model_name] = 'UNKNOWN'
                    # Continue to the next iteration.
                    continue
            
                stdout = result.stdout.decode('UTF-8')
                time_list = re.findall('time = ' + r'\d+\.\d+', stdout)
                if len(time_list):
                    elapsed_time = time_list[-1].split('= ')[-1]
                    print(f'\tSolved in {elapsed_time}s.')
                    instance_dict[model_name] = float(elapsed_time)
                elif 'time = exceeded' in stdout:
                    print('\tTime limit exceeded.')
                    instance_dict[model_name] = 'NaN'
                else: 
                    print('\tERROR: UNKNOWN.')
                    instance_dict[model_name] = 'UNKNOWN'
                    
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
