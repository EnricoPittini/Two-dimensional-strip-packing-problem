import argparse
import json
import os
import re
import subprocess
import sys
from amplpy import AMPL, AMPLException
import tempfile
import pandas

import utils


_SOLVER_CHOICES = ['cbc','cplex','gurobi']

#python scripts\execute_ampl.py AMPL\model_prova.mod instances\ins-1.txt cplex
def main() -> None:
    parser = argparse.ArgumentParser(description='Script for executing a VLSI AMPL model.')

    parser.add_argument('model-path', type=str, help='The model to execute.')

    parser.add_argument('instance-path', type=argparse.FileType('r', encoding='UTF-8'), help='The instance to solve.')

    parser.add_argument('solver-name', type=str, choices=_SOLVER_CHOICES, help='The solver used for optimization.')

    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('output-name', type=str, default=None, nargs='?', 
                        help='The name of the output solution.')

    parser.add_argument('--time-limit', '-t', type=int, default=300, nargs='?',
                        help='The allowed time to solve the task.', required=False)

    parser.add_argument('--no-create-output', action='store_true', 
                        help='Skip the creation of the output solution.')

    parser.add_argument('--no-visualize-output', action='store_true', 
                        help='Skip the visualization of the output solution (defaults as true if --no-create-output ' + \
                        'is passed).')
    
    #parser.add_argument('--symmetry-breaking-option', '-sbo', nargs='?',  type=int,
    #                    help='The symmetry breaking options to use for the MiniZinc model.', default=None)

    arguments = parser.parse_args()

    instance_file = vars(arguments)['instance-path']
    w, n, dims = utils.parse_instance_txt(instance_file)
    
    time_limit = arguments.time_limit
    #TODO remove
    time_limit = 300

    solver = vars(arguments)['solver-name']




    try:
        ampl = AMPL()
        ampl.set_option('solver', solver)
        if solver == 'cplex':
            ampl.set_option('cplex_options',f"timelimit={time_limit}")

        elif solver == 'cbc':
            ampl.set_option('cbc_options',f"sec={time_limit}")
        elif solver == 'gurobi':
            ampl.set_option('gurobi_options',f"timelim={time_limit}")

        ampl.read(os.path.normpath(vars(arguments)["model-path"]))
        _read_dat_file(w, n, dims, ampl)
        #print(ampl.get_value('solve_result'))
        # Solve
        #TODO start and stop timer
        
        ampl.solve()

        #TODO time refactor
        
        result = ampl.get_value('solve_result')
        if result == 'infeasible':
            sys.exit('ERROR: UNSATISFIABLE')
        elif result == 'limit':
            print('% Time limit exceeded!')
        elif result == 'solved':
            print(ampl.get_value('_total_solve_time'))
        else:
            sys.exit('ERROR: UNKOWN')


        l = ampl.get_value('l')
        coordsX = ampl.get_data('coordsX').to_pandas().coordsX.values
        coordsY = ampl.get_data('coordsY').to_pandas().coordsY.values
        coordsX = coordsX.astype(int)
        coordsY = coordsY.astype(int)
        l = int(l)
        print(f'l={l}')
        print(f'CoordsX={coordsX}')
        print(f'CoordsY={coordsY}')
    except AMPLException:
        sys.exit('ERROR: UNKNOWN')

    #TODO generalize
    if not arguments.no_create_output:
        
        output_folder_path = vars(arguments)['output-folder-path']

        instance_file_name = os.path.basename(instance_file.name)
        output_name = vars(arguments)['output-name']
        if output_name is None:
            output_file = os.path.join(output_folder_path, f'solution-{instance_file_name}')
        else:
            output_file = os.path.join(output_folder_path, f'{output_name}.txt')

        try:
            utils.create_output_file(output_file, w, n, dims, l, coordsX, coordsY)
        except FileNotFoundError:
            sys.exit(f'Output path {output_folder_path} does not exist.')
    
        if not arguments.no_visualize_output:
            scripts_folder = os.path.dirname(__file__)
            visualize_script_path = os.path.join(scripts_folder,'visualize.py')
            os.system(f'python {visualize_script_path} "{output_file}"')

def _read_dat_file(w, n, dims, ampl):         
    
    #TODO delete file
    
    with open('data.dat','w') as fp:
        fp.write('data;\n')
        fp.write(f'param n := {n};\n')
        fp.write(f'param w := {w};\n')
        fp.write('param: dimsX dimsY :=\n')
        for i, dim in enumerate(dims):
            fp.write(f'{i+1}\t\t{dim[0]}\t\t{dim[1]}\n')
        fp.write(';')
    ampl.read_data('data.dat')
    
if __name__ == '__main__':
    main()
