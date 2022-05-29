import argparse
from cgi import print_environ_usage
import subprocess
import json
import sys
import os

import importlib

from vlsi_sat0 import *

import time

import utils
#python scripts\execute_sat.py sat\vlsi_sat0.py minizinc\instances\ins-1.txt 

def main():
    parser = argparse.ArgumentParser(description='Script for executing a VLSI SAT encoding.')

    parser.add_argument('encoding-path', type=str, help='The encoding to execute.')

    parser.add_argument('instance-path', type=argparse.FileType('r', encoding='UTF-8'), help='The instance to solve.')

    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('--no-create-output', action='store_true', 
                        help='Skip the creation of the output solution.')

    parser.add_argument('--no-visualize-output', action='store_true', 
                        help='Skip the visualization of the output solution (defaults as true if `--no-create-output` ' + \
                        'is passed).')

    arguments = parser.parse_args()

    instance_file = vars(arguments)['instance-path']
    w, n, dims = utils.parse_instance_txt(instance_file)
    w = int(w)
    n = int(n)
    dims = [(int(dims[i][0]),int(dims[i][1])) for i in range(n)]

    #encoding_file = importlib.import_module(vars(arguments)['encoding-path'])
    #vlsi_sat = encoding_file.vlsi_sat

    try:
        start_time = time.time()
        coords, l = vlsi_sat(w, n, dims)
        solving_time =time.time() - start_time
        coordsX = [coords[i][0] for i in range(n)]
        coordsY = [coords[i][1] for i in range(n)]
        print(solving_time)
    except UnsatError:
        sys.exit('UNSAT')

    if not arguments.no_create_output:
        output_folder_path = vars(arguments)['output-folder-path']

        instance_file_name = os.path.basename(instance_file.name)
        output_file = os.path.join(output_folder_path,f'solution-{instance_file_name}')#f'{output_folder_path}\\solution-{instance_file.name.split("/")[-1]}'

        try:
            utils.create_output_file(output_file, w, n, dims, l, coordsX, coordsY)
        except FileNotFoundError as e:
            #print(e) 
            sys.exit(f'Output path {output_folder_path} does not exist.')
    
        if not arguments.no_visualize_output:
            scripts_folder = os.path.dirname(sys.argv[0])
            visualize_script_path = os.path.join(scripts_folder,'visualize.py')
            print(output_file)
            os.system(f'python {visualize_script_path} "{output_file}"')


if __name__ == "__main__":
    main()