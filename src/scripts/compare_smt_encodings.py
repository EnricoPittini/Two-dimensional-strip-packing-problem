import argparse
import json
import os
import re
import subprocess

import utils

ENCODING_CHOICES = [f'encoding_{i}' for i in range(2)] + [f'encoding_{2}{i}' for i in ['A', 'B', 'C']] +\
     [f'encoding_{3}{i}' for i in ['A', 'B', 'C', 'D', 'E', 'F']] + [f'encoding_{4}{i}' for i in ['A', 'B', 'C', 'D', 'E', 'F']] +\
        ['encoding_5A', 'encoding_5B']

def main() -> None:
    """Compare the specified SMT encodings in solving the specified VLSI problem instances.

    Example of usage: python src/scripts/compare_smt_encodings.py --encodings-list encoding_1 encoding_2A encoding_2B encoding_2C encoding_2D --solvers-list z3 -lb 1 -ub 20

    Help: python src/scripts/compare_smt_encodings.py -h

    Full list of available SMT encodings: see `ENCODINGS RECAP.md` inside the `smt` folder.
    
    """
    parser = argparse.ArgumentParser(description='Script comparing the execution time of SMT encodings on a VLSI problem.')

    parser.add_argument('output-name', type=str, default='results', nargs='?', 
                        help='The name of the output file.')

    parser.add_argument('output-folder-path', type=str, 
                        default=os.path.normpath('results/smt/'), 
                        nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('--encodings-list', '-m',  metavar='encoding', type=str, choices=utils.SMT_ENCODINGS,
                        default=['encoding_2C'],
                        help='List of SMT encodings to compare.',
                        nargs='*')
    
    parser.add_argument('--solvers-list', '-s', choices=utils.SMT_SOLVERS,
                        metavar='solver',
                        default=['z3'],
                        type=str, 
                        help='List of SMT solvers to use for comparison.',
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
    #print(output_file)
    
    encodings_list = arguments.encodings_list
    
    solvers_list = arguments.solvers_list
    
    instances_lower_bound = arguments.instances_lower_bound
    instances_upper_bound = arguments.instances_upper_bound
    if instances_lower_bound > instances_upper_bound:
        parser.error(f'argument --instances-lower-bound/-lb: invalid choice: {instances_lower_bound} ' 
                     f'(must be lower or equal than --instances-upper-bound/-ub: {instances_upper_bound})')
    instances_range = range(instances_lower_bound, instances_upper_bound + 1) 
    
    execute_smt_script_path = os.path.join(os.path.dirname(__file__), 'execute_smt.py')

    result_dict = dict()

    for instance in instances_range:
        instance_dict = dict()
        for encoding in encodings_list:
            for solver in solvers_list:
                print(f'Executing instance {instance} with encoding {encoding} with solver {solver}...')
                
                command = f'python "{execute_smt_script_path}" {encoding} ins-{instance} {solver} --no-create-output'
                
                result = subprocess.run(command, capture_output=True)
                           
                stdout = result.stdout.decode('UTF-8')
                time_list = re.findall('Time: ' + r'\d+\.\d+', stdout)
                if 'Time elapsed' in stdout:
                    print('\tTime limit exceeded.')
                    instance_dict[f'{encoding}_{solver}'] = 'NaN'
                elif len(time_list):
                    elapsed_time = time_list[-1].split('Time: ')[-1]
                    print(f'\tSolved in {elapsed_time}s.')
                    instance_dict[f'{encoding}_{solver}'] = float(elapsed_time)
                else: 
                    print('\tERROR: UNKNOWN.')
                    instance_dict[f'{encoding}_{solver}'] = 'UNKNOWN'
                    
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