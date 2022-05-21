import argparse
import subprocess
import json
import os
import sys
import re
from tokenize import Number

from numpy import number
#python scripts/compare_minizinc_models.py minizinc minizinc/instances minizinc output/

# Mega file con per ogni Istanza + [modelli + tempi]

def main():
    parser = argparse.ArgumentParser(description='Script for executing a VLSI MiniZinc model.')

    parser.add_argument('models-folder-path', type=str, help='The folder path of the models to compare.')

    parser.add_argument('instances-folder-path', type=str, help='The folder path of the instances to solve.')

    parser.add_argument('solvers-folder-path', type=str, help='The folder path of the solvers used for optimization.')

    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    # TODO: handle models string structure with a regexp possibly (model_x / model_x.mzn?)
    parser.add_argument('models-list', type=list,
                        #default=['model_0', 'model_1', 'model_2', 'model_3', 'model_4_geocode'], 
                        default=['model_0', 'model_1', 'model_2'], 
                        help='The models to compare.', nargs='*')

    parser.add_argument('instances-list', type=list, #default=[*range(10,31)], #default=' '.join([*range(10,31)]), nargs='?', 
                        default=[*range(1, 5)],
                        help='The instances to solve.', nargs='*')
    

    arguments = parser.parse_args()
    
    instances_folder_path = vars(arguments)['instances-folder-path']

    models_folder_path = vars(arguments)['models-folder-path']

    solvers_folder_path = vars(arguments)['solvers-folder-path']

    output_folder_path = vars(arguments)['output-folder-path']

    execute_minizinc_script_path = os.path.join(os.path.dirname(__file__), 'execute_minizinc.py')

    result_list = []
    
    # TODO: handling of error solutions
    # TODO: handling of parameters (instance and parameters list)
    # TODO: Handle exit codes returned by file system.
    # TODO: Handle times and output failure if UNSAT or errors.
    for instance in vars(arguments)['instances-list']:
        instance_file_path = os.path.join(instances_folder_path, f'ins-{instance}.txt')
        instance_dict = dict()
        for model in vars(arguments)['models-list']:
            model_file_path = os.path.join(models_folder_path, f'{model}.mzn')
        
            if 'gecode' in model.lower():
                solver_file_path = os.path.join(solvers_folder_path, f'solver_0.mpc')
            else:
                solver_file_path = os.path.join(solvers_folder_path, f'solver_1.mpc')
            
            #output_subfolder_path = os.path.join(output_folder_path, f'ins-{instance}/{model}/')
            
            command = f'python "{execute_minizinc_script_path}" "{model_file_path}" "{instance_file_path}" ' + \
                        f'"{solver_file_path}" --no-create-output'
            result = subprocess.run(command, stdout=subprocess.PIPE)
            output = result.stdout.decode('UTF-8')
            time_list = re.findall('\d+\.\d+', output)
            if len(time_list):
                instance_dict[model] = float(time_list[0])
            else:
                instance_dict[model] = 'NaN'
            #f.write(f'instance {instance} {model} {output}')
        result_list.append({f'ins-{instance}': instance_dict})

    output_file = os.path.join(output_folder_path, 'solution.json')

    os.makedirs(os.path.dirname(output_folder_path), exist_ok=True)

    with open(output_file, 'w') as f:
        json.dump(result_list, f, sort_keys=False, indent=4, separators=(',', ': '))


if __name__ == "__main__":
    main()