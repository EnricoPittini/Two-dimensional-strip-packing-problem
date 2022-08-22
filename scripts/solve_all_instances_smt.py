import argparse
import os
import subprocess

from utils import INSTANCES


# python scripts/solve_all_instances_smt.py
def main() -> None:
    parser = argparse.ArgumentParser(description='Script to solve all the instances using SMT.')

    parser.add_argument('output-folder-path', type=str, 
                        default=os.path.normpath('solutions/smt/'), 
                        nargs='?', 
                        help='The path in which the output files are stored.')

    parser.add_argument('--rotation', action='store_true', 
                        help='Allow the circuits rotation.')

    arguments = parser.parse_args()
    
    if not arguments.rotation:
        output_folder_path = vars(arguments)['output-folder-path']
        os.makedirs(output_folder_path, exist_ok=True)
        
        ENCODING = 'encoding_2C'
        SOLVER = 'z3'
    else:
        output_folder_path = os.path.normpath('solutions/smt_rotation')
        os.makedirs(output_folder_path, exist_ok=True)
        
        ENCODING = 'encoding_5B'
        SOLVER = 'z3'

    INSTANCES.remove('ins-unsat')
    
    execute_smt_script_path = os.path.join(os.path.dirname(__file__), 'execute_smt.py')

    for instance in INSTANCES:
        print(f'Solving instance {instance}...')
        command = f'python "{execute_smt_script_path}" {ENCODING} {instance} {SOLVER} 300 {output_folder_path} ' +\
                    '--no-visualize-output'
        if arguments.rotation: 
            command += ' --rotation'
        #print(command)
        
        try:
            subprocess.run(command, capture_output=True)
        except KeyboardInterrupt:
            continue

if __name__ == '__main__':
    main()
