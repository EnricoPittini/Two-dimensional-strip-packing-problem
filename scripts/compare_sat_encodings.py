import argparse
import json
import os
import re
import subprocess


ENCODING_CHOICES = [f'encoding_{i}' for i in range(4)] + [f'encoding_{4}{i}' for i in ['A', 'B', 'C', 'D', 'E', 'F']] +\
    ['encoding_5'] + ['encoding_6A', 'encoding_6B'] + [f'encoding_{7}{i}' for i in ['A', 'B', 'C', 'D']] +\
        [f'encoding_{8}{i}' for i in ['A', 'B', 'C', 'D', 'E']] +  ['encoding_10A', 'encoding_10B']

#python scripts/compare_sat_encodings.py sat instances sat/results/ --encodings-list encoding_3 encoding_4A encoding_4B encoding_4C encoding_4D -lb 1 -ub 15

def main() -> None:
    parser = argparse.ArgumentParser(description='Script for comparing VLSI SAT encodings.')

    parser.add_argument('encodings-folder-path', type=str, help='The folder path of the encodings to compare.')

    parser.add_argument('instances-folder-path', type=str, help='The folder path of the instances to solve.')

    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file, containing the results of the comparisons, is stored.')

    parser.add_argument('--encodings-list', '-m',
                        metavar='encoding',
                        type=str, 
                        choices=ENCODING_CHOICES,
                        # TODO: add all possible encoding choices
                        default=['encoding_0', 'encoding_1', 'encoding_2', 'encoding_3'], #'encoding_4_gecode'
                        help='List of encodings to compare (default all encodings). ' +\
                        'Example of usage: --encodings-list encoding_0 encoding_2 encoding_3',
                        nargs='*')

    parser.add_argument('--instances-lower-bound', '-lb',
                        metavar='1..40',
                        type=int,
                        choices=range(1, 42),
                        default=1,
                        help='Lower bound of instances to solve (default 1).',
                        nargs='?')

    parser.add_argument('--instances-upper-bound', '-ub', 
                        metavar='1..40',
                        type=int,
                        choices=range(1, 42),  # TODO change
                        default=40,
                        help='Upper bound of instances to solve (default 40).', 
                        nargs='?')

    arguments = parser.parse_args()
    
    instances_folder_path = vars(arguments)['instances-folder-path']

    encodings_folder_path = vars(arguments)['encodings-folder-path']

    output_folder_path = vars(arguments)['output-folder-path']

    execute_sat_script_path = os.path.join(os.path.dirname(__file__), 'execute_sat.py')

    result_list = []

    encodings_list = arguments.encodings_list
    
    instances_lower_bound = arguments.instances_lower_bound
    instances_upper_bound = arguments.instances_upper_bound
    if instances_lower_bound > instances_upper_bound:
        parser.error(f'argument --instances-lower-bound/-lb: invalid choice: {instances_lower_bound} ' 
                     f'(must be lower or equal than --instances-upper-bound/-ub: {instances_upper_bound})')
    
    instances_range = range(instances_lower_bound, instances_upper_bound + 1) 

    # TODO: handling of error solutions
    for instance in instances_range:
        instance_file_path = os.path.join(instances_folder_path, f'ins-{instance}.txt')
        instance_dict = dict()
        for encoding in encodings_list:
            encoding_file_path = os.path.join(encodings_folder_path, f'{encoding}.mzn')

            print(f'Executing instance {instance} with encoding {encoding}...')
            command = f'python "{execute_sat_script_path}" "{encoding_file_path}" "{instance_file_path}" ' +\
                       '--no-create-output'
            result = subprocess.run(command, capture_output=True)
            
            output = result.stdout.decode('UTF-8')
            #print(output)
            if 'Time elapsed' in output:
                instance_dict[encoding] =  'NaN'
            else:
                #print(output)
                #print(output.split('Time: ')[-1].split('UNSAT'))
                t = float(output.split('Time: ')[-1].split('UNSAT')[0])
                instance_dict[encoding] = t
                
        result_list.append({f'ins-{instance}': instance_dict})

    output_file = os.path.join(output_folder_path, 'results.json')

    os.makedirs(os.path.dirname(output_folder_path), exist_ok=True)

    with open(output_file, 'w') as f:
        json.dump(result_list, f, sort_keys=False, indent=4, separators=(',', ': '))

if __name__ == '__main__':
    main()
