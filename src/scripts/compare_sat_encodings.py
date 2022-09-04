import argparse
import json
import os
import re
import subprocess

import utils


def main() -> None:
    """Compare the specified SAT encodings in solving the specified VLSI problem instances.

    Example of usage: python src/scripts/compare_sat_encodings.py --encodings-list encoding_3 encoding_4A encoding_4B encoding_4C encoding_4D -lb 1 -ub 15

    Help: python src/scripts/compare_sat_encodings.py -h

    Full list of available SAT encodings: see `ENCODINGS RECAP.md` inside the `sat` folder.
    
    """
    parser = argparse.ArgumentParser(description='Script for comparing VLSI SAT encodings.')

    parser.add_argument('output-name', type=str, default='results', nargs='?', 
                        help='The name of the output file.')

    parser.add_argument('output-folder-path', type=str, 
                        default=os.path.normpath('results/sat/'), 
                        nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('--encodings-list', '-m', metavar='encoding', type=str, choices=utils.SAT_ENCODINGS,
                        default=['encoding_10B'],
                        help='List of SAT encodings to compare.',
                        nargs='*')

    parser.add_argument('--instances-lower-bound', '-lb',
                        metavar='1..40',
                        type=int,
                        choices=range(1,41),
                        default=1,
                        help='Lower bound of instances to solve (default 1).',
                        nargs='?')

    parser.add_argument('--instances-upper-bound', '-ub', 
                        metavar='1..40',
                        type=int,
                        choices=range(1,41), 
                        default=40,
                        help='Upper bound of instances to solve (default 40).', 
                        nargs='?')

    parser.add_argument('--no-visualize', action='store_true', help='Do not visualize the obtained comparisons.')

    arguments = parser.parse_args()

    output_folder_path = vars(arguments)['output-folder-path']
    output_file_name = vars(arguments)['output-name']
    output_file = os.path.join(output_folder_path, f'{output_file_name}.json')
    os.makedirs(output_folder_path, exist_ok=True)

    encodings_list = arguments.encodings_list
        
    instances_lower_bound = arguments.instances_lower_bound
    instances_upper_bound = arguments.instances_upper_bound
    if instances_lower_bound > instances_upper_bound:
        parser.error(f'argument --instances-lower-bound/-lb: invalid choice: {instances_lower_bound} ' 
                     f'(must be lower or equal than --instances-upper-bound/-ub: {instances_upper_bound})')
    
    instances_range = range(instances_lower_bound, instances_upper_bound + 1) 

    execute_sat_script_path = os.path.join(os.path.dirname(__file__), 'execute_sat.py')

    result_dict = dict()

    for instance in instances_range:
        instance_dict = dict()
        for encoding in encodings_list:
                print(f'Executing instance {instance} with encoding {encoding} ...')
                
                command = f'python "{execute_sat_script_path}" {encoding} ins-{instance} --no-create-output'
                
                result = subprocess.run(command, capture_output=True)
                           
                stdout = result.stdout.decode('UTF-8')
                time_list = re.findall('Time: ' + r'\d+\.\d+', stdout)
                if 'Time elapsed' in stdout:
                    print('\tTime limit exceeded.')
                    instance_dict[f'{encoding}'] = 'NaN'
                elif len(time_list):
                    elapsed_time = time_list[-1].split('Time: ')[-1]
                    print(f'\tSolved in {elapsed_time}s.')
                    instance_dict[f'{encoding}'] = float(elapsed_time)
                else: 
                    print('\tERROR: UNKNOWN.')
                    instance_dict[f'{encoding}'] = 'UNKNOWN'
                    
        result_dict[f'ins-{instance}'] = instance_dict

        # Save intermediate JSON solution.
        with open(output_file, 'w') as f:
            json.dump(result_dict, f, sort_keys=False, indent=4, separators=(',', ': '))

    if not arguments.no_visualize:
        plot_comparisons_path = os.path.join(os.path.dirname(__file__), 'plot_comparisons.py')
        command = f'python {plot_comparisons_path} "{output_file}"'
        subprocess.run(command)

if __name__ == '__main__':
    main()
