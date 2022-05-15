import argparse
import utils

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as patches
import matplotlib as mpl
from matplotlib.collections import PatchCollection

import random

#python scripts\visualize.py solution-ins-12.txt

def main():
    parser = argparse.ArgumentParser(description='Script for visualizing a VLSI output solution.')

    parser.add_argument('output-path', type=str, help='The output solution to visualize.')

    arguments = parser.parse_args()

    w, l, n, dims, coordsX, coordsY = utils.parse_output_file(vars(arguments)['output-path'])
    # print(w, l, n, dims, coordsX, coordsY)

    fig = plt.figure()
    ax = fig.add_subplot(111)

    plt.xlim(0, w)
    plt.ylim(0, l)
    plt.grid(True, color='black')

    myPatches = []
    # myColors = []

    for i in range(n):
        xi_hat = coordsX[i]
        yi_hat = coordsY[i]
        xi = dims[i][0]
        yi = dims[i][1]

        r = patches.Rectangle((xi_hat, yi_hat), xi, yi)
        myPatches.append(r)

    collection = PatchCollection(myPatches, cmap=mpl.cm.hsv, alpha=0.5, edgecolor='black', linewidth=4)
    collection.set_array(np.linspace(0, 254, n, dtype=int))
    #print(np.linspace(0, 200, n, dtype=int))
    collection.set_clim([0, 255])
    ax.add_collection(collection)

    plt.xticks(range(w+1))
    plt.yticks(range(l+1))

    plt.gca().set_aspect('equal', adjustable='box')

    # fig.savefig('figure.png')
    plt.show()


    


if __name__ == "__main__":
    main()