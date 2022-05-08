import argparse
import io
import subprocess
import json
import sys


def parse_instance_txt(instance_txt: io.TextIOWrapper):
    # TODO add try-except
    values = instance_txt.read().split()
    w = values[0]
    n = values[1]

    dims = []
    for i in range(int(n)):
        dims.append((values[2 * i + 2], values[2 * i + 3]))

    return w, n, dims


def create_output_file(output_file, w, n, dims, l, coordsX, coordsY):
    with open(output_file, 'w') as f:
        f.write(f'{w} {l}\n')
        f.write(f'{n}\n')
        for i in range(int(n)):
            f.write(f'{dims[i][0]} {dims[i][1]} {coordsX[i]} {coordsY[i]}\n')