import argparse
import matplotlib as mpl
import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib.collections import PatchCollection
import numpy as np
import os

import utils


def main() -> None:
    """Visualize the specified VLSI problem instance solution.

    Example of usage: python src\scripts\visualize.py solution-ins-12.txt

    Help: python src\scripts\visualize.py -h

    """
    parser = argparse.ArgumentParser(description='Script for visualizing a VLSI output solution.')

    parser.add_argument('output-path', type=str, help='The output solution to visualize.')

    arguments = parser.parse_args()
    
    output_path = vars(arguments)['output-path']

    w, l, n, dims, coordsX, coordsY = utils.parse_output_file(output_path)
    # print(w, l, n, dims, coordsX, coordsY)

    fig = plt.figure()
    ax = fig.add_subplot(111)

    plt.xlim(0, w)
    plt.ylim(0, l)
    plt.grid(True, color='black')

    patch_list = []
    # myColors = []

    for i in range(n):
        xi_hat = coordsX[i]
        yi_hat = coordsY[i]
        xi = dims[i][0]
        yi = dims[i][1]

        r = patches.Rectangle((xi_hat, yi_hat), xi, yi)
        patch_list.append(r)

    collection = PatchCollection(patch_list, cmap=mpl.cm.hsv, alpha=0.5, edgecolor='black', linewidth=4)
    collection.set_array(np.linspace(0, 254, n, dtype=int))
    #print(np.linspace(0, 200, n, dtype=int))
    collection.set_clim([0, 255])
    ax.add_collection(collection)

    plt.xticks(range(w+1))
    plt.yticks(range(l+1))

    plt.gca().set_aspect('equal', adjustable='box')

    plt.title(os.path.basename(output_path.replace('.txt','')))
    # fig.savefig('figure.png')
    plt.show()

if __name__ == '__main__':
    main()
