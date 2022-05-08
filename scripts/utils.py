import argparse
import io
import subprocess
import json
import sys


def parse_instance_txt(instance_txt_file: io.TextIOWrapper):
    # TODO add try-except
    values = instance_txt_file.read().split()
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

def parse_output_file(output_file_path):
    with open(output_file_path, 'r') as f:
        values = f.read().split()
        w = int(values[0])
        l = int(values[1])
        n = int(values[2])

        dims = []
        coordsX = []
        coordsY = []
        for i in range(int(n)):
            dims.append((int(values[4 * i + 3]), int(values[4 * i + 4])))
            coordsX.append(int(values[4 * i + 5]))
            coordsY.append(int(values[4 * i + 6]))

        # print(w, l, n, dims, coordsX, coordsY)
        return w, l, n, dims, coordsX, coordsY
