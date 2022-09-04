import argparse
import os
import subprocess

from utils import INSTANCES


# python src\scripts/solve_all_instances_sat.py
def main() -> None:
    parser = argparse.ArgumentParser(description='Script to solve all the instances using SAT.')

    parser.add_argument('--rotation', action='store_true', 
                        help='Allow the circuits rotation.')

    arguments = parser.parse_args()
    
    if not arguments.rotation:
        output_folder_path = os.path.normpath('out/sat')
        ENCODING = 'encoding_10B'
    else:
        output_folder_path = os.path.normpath('out/sat-rotation')
        ENCODING = 'encoding_11B'
        
    os.makedirs(output_folder_path, exist_ok=True)

    INSTANCES.remove('ins-unsat')
    
    execute_sat_script_path = os.path.join(os.path.dirname(__file__), 'execute_sat.py')

    for instance in INSTANCES:
        print(f'Solving instance {instance}...')
        command = f'python "{execute_sat_script_path}" {ENCODING} {instance} --time-limit 300 ' +\
            f'--output-folder-path {output_folder_path} --no-visualize-output'
        
        try:
            subprocess.run(command, capture_output=True)
        except KeyboardInterrupt:
            continue

if __name__ == '__main__':
    main()
