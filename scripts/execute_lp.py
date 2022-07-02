from amplpy import AMPL, AMPLException
import argparse
import os
import sys
import time

from kiwisolver import BadRequiredStrength

from utils import INSTANCES, AMPL_MODEL_CHOICES, AMPL_SOLVER_CHOICES, create_output_file, parse_instance_txt


#python scripts\execute_lp.py model_1 ins-1 cplex
def main() -> None:
    parser = argparse.ArgumentParser(description='Script for executing a VLSI AMPL model.')

    parser.add_argument('model', type=str, choices=AMPL_MODEL_CHOICES, help='The model to execute.')

    parser.add_argument('instance', metavar='ins-1..ins-40; ins-unsat', type=str, choices=INSTANCES, 
                        help='The instance to solve.')

    parser.add_argument('solver', type=str, default='cplex', nargs='?', choices=AMPL_SOLVER_CHOICES, 
                        help='The solver used for optimization.')

    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('output-name', type=str, default=None, nargs='?', 
                        help='The name of the output solution.')

    parser.add_argument('--time-limit', '-t', type=int, default=300, nargs='?',
                        help='The allowed time to solve the task in seconds.', required=False)

    parser.add_argument('--no-create-output', action='store_true', 
                        help='Skip the creation of the output solution.')

    parser.add_argument('--no-visualize-output', action='store_true', 
                        help='Skip the visualization of the output solution (defaults as true if --no-create-output ' + \
                        'is passed).')

    arguments = parser.parse_args()
    model = vars(arguments)['model']
    if model == 'model_dual':
        model = 'model_2B'
        use_dual = True
    else:
        use_dual = False
    instance = vars(arguments)['instance']
    solver = vars(arguments)['solver']
    time_limit = arguments.time_limit
    
    # Open instance file
    instance_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), f'instances/{instance}.txt')
    
    with open(instance_path,'r') as f:
        w, n, dims = parse_instance_txt(f)
    
    try:
        ampl = AMPL()
        ampl.set_option('solver', solver)

        if use_dual:
            if solver == 'cplex':
                ampl.set_option('cplex_options','dual')
            elif solver == 'gurobi':
                ampl.set_option('gurobi_options','predual 1')
            else:
                print('Ignoring dual solving option, solving with primal best model.')


        # Set solver dependent time limit option.
        if solver == 'cplex':
            ampl.set_option('cplex_options',f"timelimit={time_limit}")

        elif solver == 'cbc':
            ampl.set_option('cbc_options',f"sec={time_limit}")
        elif solver == 'gurobi':
            ampl.set_option('gurobi_options',f"timelim={time_limit}")
        else:
            parser.error(f"argument solver-name: invalid choice: '{solver}' " + 
                         f"(choose from {', '.join([f'{s}' for s in AMPL_SOLVER_CHOICES])})")

        # Read model and data files.
        ampl.read(os.path.join(os.path.dirname(os.path.dirname(__file__)), f'lp/{model}.mod'))
        _read_dat_file(w, n, dims, ampl)
        
        start_time = time.time()
        ampl.solve()
        solving_time = time.time() - start_time
        
        # Parse optimization result status.
        result = ampl.get_value('solve_result')
        if result == 'infeasible':
            sys.exit('error = UNSATISFIABLE')
        elif result == 'limit':
            print('time = exceeded')
        elif result == 'solved':
            print(f'time = {solving_time}')
        else:
            sys.exit('error = UNKOWN')

        # Parse variables results.
        l = int(ampl.get_value('l'))
        
        coordsX = ampl.get_data('coordsX').to_pandas().coordsX.values
        coordsY = ampl.get_data('coordsY').to_pandas().coordsY.values
        coordsX = coordsX.astype(int)
        coordsY = coordsY.astype(int)

        print(f'l = {l}')
        print(f'CoordsX = {coordsX}')
        print(f'CoordsY = {coordsY}')
    except AMPLException:
        sys.exit('error = UNKOWN')

    #TODO generalize
    if not arguments.no_create_output:
        
        output_folder_path = vars(arguments)['output-folder-path']

        output_name = vars(arguments)['output-name']
        if output_name is None:
            output_file = os.path.join(output_folder_path, f'solution-{instance}')
        else:
            output_file = os.path.join(output_folder_path, f'{output_name}.txt')

        try:
            create_output_file(output_file, w, n, dims, l, coordsX, coordsY)
        except FileNotFoundError:
            sys.exit(f'Output path {output_folder_path} does not exist.')
    
        if not arguments.no_visualize_output:
            scripts_folder = os.path.dirname(__file__)
            visualize_script_path = os.path.join(scripts_folder,'visualize.py')
            os.system(f'python {visualize_script_path} "{output_file}"')

def _read_dat_file(w, n, dims, ampl):         
    data_file_path = 'data.dat'
    
    # Create `.dat` data file with `AMPL` required format.
    with open(data_file_path,'w') as fp:
        fp.write('data;\n')
        fp.write(f'param n := {n};\n')
        fp.write(f'param w := {w};\n')
        fp.write('param: dimsX dimsY :=\n')
        for i, dim in enumerate(dims):
            fp.write(f'{i+1}\t\t{dim[0]}\t\t{dim[1]}\n')
        fp.write(';')
    
    ampl.read_data(data_file_path)
    
    # Delete `.dat` data file.
    if os.path.exists(data_file_path):
        os.remove(data_file_path)
    
if __name__ == '__main__':
    main()
