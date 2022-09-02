import argparse
import os
import subprocess

from utils import INSTANCES


# python scripts/solve_all_instances_cp.py
def main() -> None:
    parser = argparse.ArgumentParser(description='Script to solve all the instances using CP.')

    parser.add_argument('output-folder-path', type=str, 
                        default=os.path.normpath('solutions/lp/'), 
                        nargs='?', 
                        help='The path in which the output files are stored.')
    
    parser.add_argument('--use-rotations', action='store_true', 
                        help='Solve with rotations.')

    arguments = parser.parse_args()
    
    output_folder_path = vars(arguments)['output-folder-path']
    use_rotations = arguments.use_rotations
    os.makedirs(output_folder_path, exist_ok=True)
    
    INSTANCES.remove('ins-unsat')
    
    if use_rotations:
        MODEL = 'model_r_0'
        OPTIONS = '--use-symmetry'
    else:
        MODEL = 'model_1'
        OPTIONS = ''
    
    execute_lp_script_path = os.path.join(os.path.dirname(__file__), 'execute_lp.py')
    
    for instance in INSTANCES:
        print(f'Solving instance {instance}...')
        command = f'python "{execute_lp_script_path}" {MODEL} {instance} gurobi {output_folder_path} ' +\
                    f'--time-limit 300 --no-visualize-output {OPTIONS}'
        
        try:
            subprocess.run(command, capture_output=True)
        except KeyboardInterrupt:
            continue

if __name__ == '__main__':
    main()
