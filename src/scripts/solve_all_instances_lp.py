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
        output_folder_path = os.path.normpath('out/lp')
        MODEL = 'model_1'
        OPTIONS = ''
    else:
        output_folder_path = os.path.normpath('out/lp-rotation')
        MODEL = 'model_r_0'
        OPTIONS = '--use-symmetry'

    os.makedirs(output_folder_path, exist_ok=True)
    
    INSTANCES.remove('ins-unsat')
    
    execute_lp_script_path = os.path.join(os.path.dirname(__file__), 'execute_lp.py')
    
    for instance in INSTANCES:
        print(f'Solving instance {instance}...')
        command = f'python "{execute_lp_script_path}" {MODEL} {instance} gurobi ' +\
            f'--output-folder-path {output_folder_path} --time-limit 300 --no-visualize-output {OPTIONS}'
        
        try:
            subprocess.run(command, capture_output=True)
        except KeyboardInterrupt:
            continue

if __name__ == '__main__':
    main()
