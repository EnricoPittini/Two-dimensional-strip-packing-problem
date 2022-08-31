import argparse
import os
from re import sub
import subprocess
import sys

METHODS = ['cp', 'sat', 'smt', 'lp']

def main() -> None:
    parser = argparse.ArgumentParser(description='Script to solve all the instances using a certain methodology.')

    parser.add_argument('method', type=str,
                        default='cp',
                        choices = METHODS,
                        nargs='?', 
                        help='The method to solve all the instances.')
    
    parser.add_argument('output-folder-path', type=str, 
                        default=None, 
                        nargs='?', 
                        help='The path in which the output files are stored.')
    
    parser.add_argument('--use-rotations', action='store_true', 
                        help='Solve with rotations.')

    arguments = parser.parse_args()
    method = vars(arguments)['method']
    output_folder_path = vars(arguments)['output-folder-path']
    if output_folder_path is None:
        output_folder_path = f'solutions/{method}/'
    use_rotations = arguments.use_rotations
    
    execute_script_path = os.path.dirname(__file__)
    
    if use_rotations:
        rotations_command = '--use-rotations' if method in ['cp', 'lp'] else '--rotations'
    else:
        rotations_command = ''
    
    command = f'python "{execute_script_path}/solve_all_instances_{method}.py" {output_folder_path} {rotations_command}'
    
    subprocess.run(command, stderr=sys.stderr, stdout=sys.stdout)
    """ with subprocess.Popen(command, bufsize=1, stdout=subprocess.PIPE, stderr=subprocess.PIPE) as sub:
        for line in sub.stdout.readline():
            print('here')
            print(line, end='')"""
        
if __name__ == '__main__':
    main()
