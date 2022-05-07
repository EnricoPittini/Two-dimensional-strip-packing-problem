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

    arguments = parser.parse_args()

    parsed_cmdline_data = parse_instance_txt(arguments.instance)
  
    print(parsed_cmdline_data)

    command = f'minizinc {arguments.model} {parsed_cmdline_data} --param-file {arguments.solver}'
    result = subprocess.run(command, stdout=subprocess.PIPE)
    output = result.stdout.decode('UTF-8').replace('-', '').replace('=', '')

    try:
        json_result = json.loads(output)
        print(json_result)
    except:
        sys.exit(output)

    # os.system()

def parse_instance_txt(instance_txt: io.TextIOWrapper):
    # TODO add try-except
    values = instance_txt.read().split()
    w = values[0]
    n = values[1]

    dims = []
    for i in range(int(n)):
        dims.append((values[2 * i + 2], values[2 * i + 3]))

    formatted_dims = f'[|{"|".join([",".join(d) for d in dims])}|]'
    
    PREFIX = '--cmdline-data'
    parsed_w = f'{PREFIX} "w = {w}"'
    parsed_n = f'{PREFIX} "n = {n}"'
    parsed_dims = f'{PREFIX} "dims = {formatted_dims}"'
    
    return f'{parsed_w} {parsed_n} {parsed_dims}'

if __name__ == "__main__":
    main()