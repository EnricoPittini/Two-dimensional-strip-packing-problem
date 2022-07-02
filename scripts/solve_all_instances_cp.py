import argparse
import os
import subprocess

from utils import INSTANCES


# python scripts/solve_all_instances_cp.py
def main() -> None:
    parser = argparse.ArgumentParser(description='Script to solve all the instances using CP.')

    parser.add_argument('output-folder-path', type=str, 
                        default=os.path.normpath('solutions/cp/'), 
                        nargs='?', 
                        help='The path in which the output files are stored.')

    arguments = parser.parse_args()
    
    output_folder_path = vars(arguments)['output-folder-path']
    os.makedirs(output_folder_path, exist_ok=True)
    
    MODEL = 'model_6D1'
    INSTANCES.remove('ins-unsat')
    
    execute_cp_script_path = os.path.join(os.path.dirname(__file__), 'execute_cp.py')

    for instance in INSTANCES:
        print(f'Solving instance {instance}...')
        command = f'python "{execute_cp_script_path}" {MODEL} {instance} {output_folder_path} ' +\
                    '--time-limit 300 --no-visualize-output'
        
        try:
            subprocess.run(command, capture_output=True)
        except KeyboardInterrupt:
            continue

if __name__ == '__main__':
    main()
