import argparse
import io
import subprocess
import json
import sys


def main():
    parser = argparse.ArgumentParser(description='Script for executing a VLSI MiniZinc model.')

    parser.add_argument('model', type=str, help='The model to execute.')

    parser.add_argument('instance', type=argparse.FileType('r', encoding='UTF-8'), help='The instance to solve.')

    parser.add_argument('solver', type=str, help='The solver used for optimization.')

    parser.add_argument('output-path', type=str, default='./', nargs='?', help='The path in which the output file is stored')

    arguments = parser.parse_args()

    w, n, dims = parse_instance_txt(arguments.instance)

    parsed_cmdline_data = create_cmdline_data(w, n, dims)

    command = f'minizinc {arguments.model} {parsed_cmdline_data} --param-file {arguments.solver}'
    result = subprocess.run(command, stdout=subprocess.PIPE)
    output = result.stdout.decode('UTF-8').replace('-', '').replace('=', '')

    try:
        json_result = json.loads(output)
        print(json_result)
    except:
        sys.exit(output)

    l = json_result['l']
    coordsX = json_result['coordsX']
    coordsY = json_result['coordsY']

    output_path = vars(arguments)["output-path"]
    if output_path[-1] != '/':
        output_path += '/'
    output_file = f'{output_path}solution-{arguments.instance.name.split("/")[-1]}'

    try:
        create_output_file(output_file, w, n, dims, l, coordsX, coordsY)
    except FileNotFoundError: 
        sys.exit(f'Output path {output_path} does not exist.')


def parse_instance_txt(instance_txt: io.TextIOWrapper):
    # TODO add try-except
    values = instance_txt.read().split()
    w = values[0]
    n = values[1]

    dims = []
    for i in range(int(n)):
        dims.append((values[2 * i + 2], values[2 * i + 3]))

    return w, n, dims

def create_cmdline_data(w, n, dims):

    formatted_dims = f'[|{"|".join([",".join(d) for d in dims])}|]'
    
    PREFIX = '--cmdline-data'
    parsed_w = f'{PREFIX} "w = {w}"'
    parsed_n = f'{PREFIX} "n = {n}"'
    parsed_dims = f'{PREFIX} "dims = {formatted_dims}"'
    
    return f'{parsed_w} {parsed_n} {parsed_dims}'

def create_output_file(output_file, w, n, dims, l, coordsX, coordsY):
    with open(output_file, 'w') as f:
        f.write(f'{w} {l}\n')
        f.write(f'{n}\n')
        for i in range(int(n)):
            f.write(f'{dims[i][0]} {dims[i][1]} {coordsX[i]} {coordsY[i]}\n')





if __name__ == "__main__":
    main()