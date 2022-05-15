import argparse
from cgi import print_environ_usage
import subprocess
import json
import sys
import os
import re

import utils
#python scripts\execute_minizinc.py minizinc\model_1.mzn minizinc\instances\ins-13.txt minizinc\solver_0.mpc

def main():
    parser = argparse.ArgumentParser(description='Script for executing a VLSI MiniZinc model.')

    parser.add_argument('model-path', type=str, help='The model to execute.')

    parser.add_argument('instance-path', type=argparse.FileType('r', encoding='UTF-8'), help='The instance to solve.')

    parser.add_argument('solver-path', type=str, help='The solver used for optimization.')

    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored')

    arguments = parser.parse_args()

    instance_file = vars(arguments)['instance-path']
    w, n, dims = utils.parse_instance_txt(instance_file)

    parsed_cmdline_data = create_cmdline_data(w, n, dims)

    command = f'minizinc {vars(arguments)["model-path"]} {parsed_cmdline_data} --param-file {vars(arguments)["solver-path"]}'
    result = subprocess.run(command, stdout=subprocess.PIPE)
    output = result.stdout.decode('UTF-8').replace('-', '').replace('=', '')
    #print(output)
    time = output.split('%')[-1]
    output = output.split('%')[0]
    print(time)
    #print(output)
    try:
        json_result = json.loads(output)
        print(json_result)
    except:
        print('Warning:')
        sys.exit(output)

    l = json_result['l']
    coordsX = json_result['coordsX']
    coordsY = json_result['coordsY']

    output_folder_path = vars(arguments)['output-folder-path']
    #if output_folder_path[-1] != '\\':
    #   output_folder_path += '\\'
    instance_file_name = os.path.basename(instance_file.name)
    output_file = os.path.join(output_folder_path,f'solution-{instance_file_name}')#f'{output_folder_path}\\solution-{instance_file.name.split("/")[-1]}'

    try:
        utils.create_output_file(output_file, w, n, dims, l, coordsX, coordsY)
    except FileNotFoundError as e:
        print(e) 
        #sys.exit(f'Output path {output_folder_path} does not exist.')


def create_cmdline_data(w, n, dims):

    formatted_dims = f'[|{"|".join([",".join(d) for d in dims])}|]'
    
    PREFIX = '--cmdline-data'
    parsed_w = f'{PREFIX} "w = {w}"'
    parsed_n = f'{PREFIX} "n = {n}"'
    parsed_dims = f'{PREFIX} "dims = {formatted_dims}"'
    
    return f'{parsed_w} {parsed_n} {parsed_dims}'


if __name__ == "__main__":
    main()