from amplpy import AMPL, AMPLException
import argparse
import importlib
import numpy as np
import os
import sys
import time

from utils import INSTANCES, AMPL_MODEL_CHOICES, AMPL_SOLVER_CHOICES, create_output_file, parse_instance_txt

module_name = 'position_and_covering'
sys.path.insert(1,  os.path.join(os.path.dirname(os.path.dirname(__file__)), 'lp'))
encoding_module = importlib.import_module(module_name)
apply_position_and_covering = encoding_module.apply_position_and_covering


#python src\scripts\execute_lp.py model_1 ins-1 cplex
def main() -> None:
    parser = argparse.ArgumentParser(description='Script for executing a VLSI AMPL model.')

    parser.add_argument('model', metavar='model', type=str, choices=AMPL_MODEL_CHOICES, help='The model to execute.')

    parser.add_argument('instance', metavar='instance', type=str, choices=INSTANCES, 
                        help='The instance to solve.')

    parser.add_argument('solver', metavar='solver', type=str, default='cplex', nargs='?', choices=AMPL_SOLVER_CHOICES, 
                        help='The solver used for optimization.')

    parser.add_argument('--output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('--output-name', type=str, default=None, nargs='?', 
                        help='The name of the output solution.')

    parser.add_argument('--time-limit', '-t', type=int, default=300, nargs='?',
                        help='Time limit, in seconds', required=False)

    parser.add_argument('--no-create-output', action='store_true', 
                        help='Skip the creation of the output solution.')

    parser.add_argument('--no-visualize-output', action='store_true', 
                        help='Skip the visualization of the output solution (defaults as true if --no-create-output ' + \
                        'is passed).')

    parser.add_argument('--use-symmetry', action='store_true', 
                    help='Break symmetries in the presolve process.')

    parser.add_argument('--use-dual', action='store_true', 
                    help='Use the dual model.')

    parser.add_argument('--use-no-presolve', action='store_true', 
                    help='Avoid AMPL presolving process.')

    arguments = parser.parse_args()
    model = vars(arguments)['model']
    
    use_symmetry = arguments.use_symmetry
    use_dual = arguments.use_dual
    use_no_presolve = arguments.use_no_presolve
    use_rotations = '_r_' in model
        
    instance = vars(arguments)['instance']
    solver = vars(arguments)['solver']
    time_limit = arguments.time_limit
    
    # Open instance file
    instance_path = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(__file__))), f'instances/{instance}.txt')
    
    with open(instance_path,'r') as f:
        w, n, dims = parse_instance_txt(f)
    
    w = int(w); n = int(n); dims = [(int(d[0]), int(d[1])) for d in dims]
    
    try:
        ampl = AMPL()
        ampl.set_option('solver', solver)
        
        cplex_options = []
        gurobi_options = []
        
        if use_symmetry:
            if solver == 'cplex':
                cplex_options.append('symmetry=5')
            elif solver == 'gurobi':
                gurobi_options.append('symmetry=2')
            else:
                print('Ignoring symmetry solving option.')
                
        if use_no_presolve:
            ampl.set_option('presolve', 0)

        if use_dual:
            if solver == 'cplex':
                cplex_options.append('dual')
            elif solver == 'gurobi':
                gurobi_options.append('predual=1')
            else:
                print('Ignoring dual solving option, solving with primal best model.')

        # Set solver dependent time limit option.
        if solver == 'cplex':
            ampl.set_option('cplex_options', ' '.join(cplex_options) + f" timelimit={time_limit}")
        elif solver == 'cbc':
            ampl.set_option('cbc_options', f"sec={time_limit}")
        elif solver == 'gurobi':
            ampl.set_option('gurobi_options', ' '.join(gurobi_options) + f" timelim={time_limit}")
        else:
            parser.error(f"argument solver-name: invalid choice: '{solver}' " + 
                         f"(choose from {', '.join([f'{s}' for s in AMPL_SOLVER_CHOICES])})")
        
        ampl.read(os.path.join(os.path.dirname(os.path.dirname(__file__)), f'lp/{model}.mod'))
        
        _set_model_main_params(w, n, dims, ampl, model)
        
        if 'grid' in model:
            dims, coordsX, coordsY, l, solving_time = apply_position_and_covering(
                w, n, dims, ampl, solver, time_limit, use_rotations, cplex_options, gurobi_options)
            if solving_time is None:
                sys.exit('error = UNKOWN')
            else:
                print(f'time = {solving_time}')
        else:
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
            
            if use_rotations:
                dimsX = ampl.get_data('actualDimsX').to_pandas().actualDimsX.values
                dimsY = ampl.get_data('actualDimsY').to_pandas().actualDimsY.values
                dimsX = dimsX.astype(int)
                dimsY = dimsY.astype(int)
                dims = list(zip(dimsX, dimsY))
            
            coordsX = ampl.get_data('coordsX').to_pandas().coordsX.values
            coordsY = ampl.get_data('coordsY').to_pandas().coordsY.values
            coordsX = coordsX.astype(int)
            coordsY = coordsY.astype(int)

        print(f'l = {l}')
        print(f'CoordsX = {coordsX}')
        print(f'CoordsY = {coordsY}')
    except AMPLException:
        sys.exit('error = UNKOWN')

    if not arguments.no_create_output:
        output_folder_path = arguments.output_folder_path

        output_name = arguments.output_name
        if output_name is None:
            output_file = os.path.join(output_folder_path, f'solution-{instance}.txt')
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

def _set_model_main_params(w, n, dims, ampl, model):
    """Set the main parameters of the `AMPL` model.

    Parameters
    ----------
    w : int
        The width of the plate
    n : int
        The number of circuits
    dims : list of tuple of int
        Dims X and Y (i.e. width and height) of the circuits
    ampl : AMPL
        An AMPL translator
    """
    ampl.param['n'] = n
    ampl.param['w'] = w
    if 'grid' not in model:
        ampl.param['dimsX'] = [d[0] for d in dims]
        ampl.param['dimsY'] = [d[1] for d in dims]
    if model in ['model_2']:
        ampl.param['maxAreaIndex'] = int(np.argmax([d[0]*d[1] for d in dims]) + 1)
    if model in ['model_1', 'model_2']:
        k = w // max([d[0] for d in dims])
        if k == 1:
            l_max = sum([d[1] for d in dims]) 
        else: 
            l_max = sum([d for i, d in enumerate(sorted([d[1] for d in dims], reverse=True)) if i % k == 0]) 
        ampl.param['lMax'] = l_max
        l_min = max(max([d[1] for d in dims]), sum([d[0]*d[1] for d in dims]) // w)
        ampl.param['lMin'] = l_min
    if model == 'model_r_0':
        maxDims = [max(d[0], d[1]) for d in dims]
        k = w // max(maxDims)
        if k < 2:
            l_max = sum(maxDims) 
        else: 
            l_max = sum([d for i, d in enumerate(sorted(maxDims, reverse=True)) if i % k == 0]) 
        ampl.param['lMax'] = l_max
        l_min = sum([d[0]*d[1] for d in dims]) // w
        ampl.param['lMin'] = l_min

if __name__ == '__main__':
    main()
