import argparse
import os
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
    
    parser.add_argument('--rotation', action='store_true', help='Allow the circuits rotation.')

    arguments = parser.parse_args()
    method = vars(arguments)['method']
    rotations_command = '--rotation' if arguments.rotation else ''

    execute_script_path = os.path.dirname(__file__)
    
    command = f'python "{execute_script_path}/solve_all_instances_{method}.py" {rotations_command}'
    
    subprocess.run(command, stderr=sys.stderr, stdout=sys.stdout)
        
if __name__ == '__main__':
    main()
