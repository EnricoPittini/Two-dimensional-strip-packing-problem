import argparse
import json
import matplotlib.pyplot as plt
import matplotlib.lines as mlines
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

    json_path = os.path.normpath(vars(arguments)['json-path'])

    with open(json_path, 'r') as j:
        comparison_list = json.load(j)

    instances_list = arguments.instances_list

    if instances_list is None:
        instances_lower_bound = arguments.instances_lower_bound
        instances_upper_bound = arguments.instances_upper_bound
        if instances_lower_bound > instances_upper_bound:
            parser.error(f'argument --instances-lower-bound/-lb: invalid choice: {instances_lower_bound} ' 
                        f'(must be lower or equal than --instances-upper-bound/-ub: {instances_upper_bound})')

        available_instances = [f'ins-{i}' for i in range(instances_lower_bound, instances_upper_bound + 1)]
        
        instances_list = [k for k in comparison_list if k in available_instances] # TODO: add eventual filter
    else:
        instances_list = [f'ins-{i}' for i in instances_list]
    
    models_list = arguments.models_list

    if models_list is None:
        models_dictionary = {
            m: {'time': [],  'non_optimal': [], 'not_solved': []} for c in instances_list for m in comparison_list[c]
        }
    else:
        models_dictionary = {
            m: {'time': [],  'non_optimal': [], 'not_solved': []} for m in models_list
        }
    for ins in instances_list:
        for m in models_dictionary:
            _add_model_results(comparison_list[ins], models_dictionary, m)

    fig = plt.figure(figsize=(15,6))
    ax = fig.add_subplot(111)

    ax = plt.subplot(111)

    x_axis = [i for i in range(len(instances_list))]

    if len(models_dictionary) == 1:
        offsets = np.array([0.])
    else:
        offsets = np.linspace(-0.2, 0.2, len(models_dictionary), dtype=float)

    for i, m in enumerate(models_dictionary):
        ax.bar(x_axis + offsets[i], models_dictionary[m]['time'], 
               width=0.4 / (len(models_dictionary) - 1), align='center', label=m)

    plt.axline((0, 300), slope=0, color="r", linestyle='dashed')

    for i, m in enumerate(models_dictionary):
        for j, b in enumerate(models_dictionary[m]['not_solved']):
            if b:
                ax.plot(x_axis[j] + offsets[i],  5, marker="X", linestyle=None, color="r", markeredgewidth=0.5, 
                        markeredgecolor='black', markersize=10)
        for j, b in enumerate(models_dictionary[m]['non_optimal']):
            if b:
                ax.plot(x_axis[j] + offsets[i], models_dictionary[m]['time'][j], marker="^", linestyle=None, color="orange", 
                        markeredgewidth=0.5, markeredgecolor='black', markersize=10)

    ax.set_xticks(range(len(instances_list)))
    ax.set_xticklabels(instances_list, rotation = 45, va="center", position=(0,-0.03))

    ax.set_ylim(0, 310)

    ax.set_xlabel('instances')
    ax.set_ylabel('time (s)')

    legend = ax.legend(loc='upper left')

    ax = legend.axes

    handles, labels = ax.get_legend_handles_labels()

    if True in {b for m in models_dictionary for b in models_dictionary[m]['not_solved']}:
        handles.append(mlines.Line2D([], [], color='r', marker='X', linestyle='None', markersize=10))
        labels.append("Not solved")

    if True in {b for m in models_dictionary for b in models_dictionary[m]['non_optimal']}:
        handles.append(mlines.Line2D([], [], color='orange', marker='^', linestyle='None', markersize=10))
        labels.append("Non optimal")

    legend._legend_box = None
    legend._init_legend_box(handles, labels)
    legend._set_loc(legend._loc)
    legend.set_title(legend.get_title().get_text())

    plt.show()

def _add_model_results(comparison: dict, model_dictionary: dict, model: str) -> dict:
    time_value = comparison[model]

    if type(time_value) == float:
        time_value = min(time_value, 300)
        non_optimal = False
        not_solved = False
    elif time_value == 'NaN':
        time_value = 300
        non_optimal = True
        not_solved = False
    else:
        time_value = 0
        non_optimal = False
        not_solved = True 

    for k, v in list(zip(['time', 'non_optimal', 'not_solved'], [time_value, non_optimal, not_solved])):
        model_dictionary[model][k].append(v)

if __name__ == '__main__':
    main()
