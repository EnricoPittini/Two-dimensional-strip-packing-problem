import argparse
import json
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
import numpy as np
import os

from utils import INSTANCES


def main() -> None:
    parser = argparse.ArgumentParser(description='Script for plotting a comparison between models.')

    parser.add_argument('json-path', type=str, help='The json file containing the comparisons.')

    parser.add_argument('--instances-list', '-i',
                        metavar='1..40',
                        type=int, 
                        choices=range(1,41),
                        default=None,
                        help='List of instances to plot (default None). Example of usage: --instances-list 1 2 3',
                        nargs='*')

    parser.add_argument('--instances-lower-bound', '-lb',
                        metavar='1..40',
                        type=int,
                        choices=range(1, 41),
                        default=1,
                        help='Lower bound of instances to solve (default 1). Ignored if --instances-list is provided',
                        nargs='?')

    parser.add_argument('--instances-upper-bound', '-ub', 
                        metavar='1..40',
                        type=int,
                        choices=range(1, 41),
                        default=40,
                        help='Upper bound of instances to solve (default 40). Ignored if --instances-list is provided', 
                        nargs='?')

    parser.add_argument('--models-list', '-m',
                    metavar='models...',
                    type=str,
                    default=None,
                    help='List of models to show (default None). Example of usage: --models-list model_0 model_1',
                    nargs='*')

    arguments = parser.parse_args()

    # Get JSON comparison file.
    json_path = os.path.normpath(vars(arguments)['json-path'])
    with open(json_path, 'r') as j:
        comparison_dictionary = json.load(j)

    # Get instances list.
    instances_list = arguments.instances_list

    if instances_list is None:
        instances_lower_bound = arguments.instances_lower_bound
        instances_upper_bound = arguments.instances_upper_bound
        if instances_lower_bound > instances_upper_bound:
            parser.error(f'argument --instances-lower-bound/-lb: invalid choice: {instances_lower_bound} ' 
                        f'(must be lower or equal than --instances-upper-bound/-ub: {instances_upper_bound})')

        available_instances = [f'ins-{i}' for i in range(instances_lower_bound, instances_upper_bound + 1)]
        
        instances_list = [k for k in comparison_dictionary if k in available_instances]
    else:
        instances_list = [f'ins-{i}' for i in instances_list]
    
    # Get models dictionary.
    models_dictionary = _get_models_dictionary(arguments.models_list, instances_list, comparison_dictionary)

    fig = plt.figure(figsize=(15,6))
    ax = fig.add_subplot(111)

    # Get increasing ordinal values for each instance.
    x_axis = [i for i in range(len(instances_list))]

    # Set offset of bars of the chart.
    if len(models_dictionary) == 1:
        offsets = np.array([0.])
    else:
        offsets = np.linspace(-0.2, 0.2, len(models_dictionary), dtype=float)

    # Draw times of models that found optimal solutions for each instance.
    for i, m in enumerate(models_dictionary):
        ax.bar(x_axis + offsets[i], models_dictionary[m]['time'], color=f'C{i}',
               width=0.4 / max(1, (len(models_dictionary) - 1)), align='center', label=m)
    # Draw times of models that found non-optimal solutions for each instance.
    for i, m in enumerate(models_dictionary):
        ax.bar(x_axis + offsets[i], models_dictionary[m]['non_optimal'], hatch='//', alpha=0.3, color=f'C{i}',
               width=0.4 / max(1, (len(models_dictionary) - 1)), align='center')

    # Set "time limit" horizontal line.
    plt.axline((0, 300), slope=0, color="r", linestyle='dashed')

    # Set x-ticks as the instances names.
    ax.set_xticks(range(len(instances_list)))
    ax.set_xticklabels(instances_list, rotation = 45, va="center", position=(0,-0.03))

    # Set chart visible ranges on the x and y axes.
    ax.set_xlim(-.5, len(instances_list) - .5)
    ax.set_ylim(0, 310)

    # Set axes labels
    ax.set_xlabel('instances')
    ax.set_ylabel('time (s)')

    # Set legend
    legend = ax.legend(loc='upper left')
    ax = legend.axes

    handles, labels = ax.get_legend_handles_labels()
    
    handles.append(Patch(facecolor='#DCDCDC', hatch='//'))
    labels.append('Non optimal')

    legend._legend_box = None
    legend._init_legend_box(handles, labels)
    legend._set_loc(legend._loc)
    legend.set_title(legend.get_title().get_text())

    plt.show()

def _get_models_dictionary(models_list: list, instances_list: list, comparison_dictionary: dict) -> None:
    if models_list is None:
        models_dictionary = { m: {'time': [],  'non_optimal': []} for c in instances_list for m in comparison_dictionary[c] }
    else:
        models_dictionary = { m: {'time': [],  'non_optimal': []} for m in models_list }
    
    for ins in instances_list:
        for m in models_dictionary:
            time_value = comparison_dictionary[ins][m]

            if type(time_value) == float:
                time_value = min(time_value, 300)
                non_optimal = 0

            else:
                time_value = 0
                non_optimal = 300

            for k, v in list(zip(['time', 'non_optimal'], [time_value, non_optimal])):
                models_dictionary[m][k].append(v)

    return models_dictionary

if __name__ == '__main__':
    main()
