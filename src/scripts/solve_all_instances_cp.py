import argparse
import os
import subprocess

from utils import INSTANCES


# python src/scripts/solve_all_instances_cp.py
def main() -> None:
    parser = argparse.ArgumentParser(description='Script to solve all the instances using CP.')
    
    parser.add_argument('--rotation', action='store_true', 
                        help='Solve with rotations.')

    arguments = parser.parse_args()

    if not arguments.rotation:
        output_folder_path = os.path.normpath('out/cp')
        MODEL = 'model_6D1'
    else:
        output_folder_path = os.path.normpath('out/cp-rotation')
        MODEL = 'model_r_7B'

    os.makedirs(output_folder_path, exist_ok=True)
    
    INSTANCES.remove('ins-unsat')
    
    execute_cp_script_path = os.path.join(os.path.dirname(__file__), 'execute_cp.py')

    for instance in INSTANCES:
        print(f'Solving instance {instance}...')
        command = f'python "{execute_cp_script_path}" {MODEL} {instance} --output-folder-path {output_folder_path} ' +\
                    '--time-limit 300 --no-visualize-output'
        
        try:
            subprocess.run(command, capture_output=True)
        except KeyboardInterrupt:
            continue

if __name__ == '__main__':
    main()
