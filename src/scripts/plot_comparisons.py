import argparse
import json
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
import numpy as np
import os

from utils import INSTANCES


def main() -> None:
    """Plot the specified comparison results file, about different models solving the same VLSI instances.

    Example of usage: python src\scripts\plot_comparisons.py results\smt\results_comparison_encodings_2B_2C_2D_solvers_z3.json --models-list encoding_2B_z3 encoding_2C_z3 encoding_2D_z3 -mr 'BinarySearch' 'FromTop' 'BinarySearch1'

    Help: python src\scripts\plot_comparisons.py -h

    """
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

    parser.add_argument('--model-renames', '-mr',
                    metavar='models...',
                    type=str,
                    default=None,
                    help='List of models to rename. Example of usage: -mr "model 1" "model 2" (The renaming is positional ' +
                    'and it must be the same length of the used models. Furthermore, the list of models ' +
                    '(--models-list/-m) must be provided)',
                    nargs='*')

    parser.add_argument('--title', '-t', type=str,
                        default='Models comparison',
                        help='Plot title', 
                        nargs='?')

    arguments = parser.parse_args()
    
    models_list = arguments.models_list
    model_renames = arguments.model_renames
    
    if model_renames is not None:
        if models_list is None:
            parser.error(f'argument --models-list/-m: not provided ' 
                        f'(must be explicitally provided when --model-renames/-mr is specified)')
        if len(models_list) != len(model_renames):
            parser.error(f'argument --model-renames/-mr: invalid choices: {model_renames} ' 
                        f'(must be equivalent in length to the models that will be used from the json)')

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
    models_dictionary = _get_models_dictionary(models_list, instances_list, comparison_dictionary, model_renames)

    # Rename models list.
    model_renames = arguments.model_renames
    if model_renames is not None:
        if len(models_dictionary) != len(model_renames):
            parser.error(f'argument --model-renames/-mr: invalid choices: {model_renames} ' 
                        f'(must be equivalent in length to the models that will be used from the json)')

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
    bar_colors = [f"C{i}" for i in range(len(models_dictionary))]
    for i, m in enumerate(models_dictionary):
        ax.bar(x_axis + offsets[i], models_dictionary[m]['time'], color=bar_colors[i],#color=f'C{i}',
               width=0.4 / max(1, (len(models_dictionary) - 1)), align='center')#, label=m)
    # Draw times of models that found non-optimal solutions for each instance.
    for i, m in enumerate(models_dictionary):
        ax.bar(x_axis + offsets[i], models_dictionary[m]['non_optimal'], hatch='//', alpha=0.3, color=bar_colors[i],#color=f'C{i}',
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

    ax.set_title(arguments.title)

    ax.grid()

    # Set legend
    legend = ax.legend(loc='upper left')
    ax = legend.axes

    handles, labels = ax.get_legend_handles_labels()
    
    handles.append(Patch(facecolor='#808080'))
    labels.append('Optimal')
    handles.append(Patch(facecolor='#DCDCDC', hatch='//'))
    labels.append('Non optimal')

    legend._legend_box = None
    legend._init_legend_box(handles, labels)
    #legend._set_loc(legend._loc+1)
    bbox_to_anchor=(0.01, 0.85)
    legend._set_loc(bbox_to_anchor)
    legend.set_title(legend.get_title().get_text())

    statistics_dictionary = _compute_statistics(models_dictionary)
    #print(statistics_dictionary)

    #baseline_times = execution_time_data[0]
    spaces = 3
    rows = [' ' * spaces for i in range(len(statistics_dictionary))]
    cols = ('Name', 'Solved \ninstances', 'Mean \nruntime')

    #stats = [get_timing_stats(execution_times, baseline_times) for execution_times in execution_time_data]
    t = [[s, f"{statistics_dictionary[s]['n_solved_instances']}/{len(instances_list)}", 
          f"{statistics_dictionary[s]['mean_time']:.2f} s"] for s in statistics_dictionary]
    #bar_colors = [f"C{(i+starting_color)%10}" for i in range(n_approaches)]
    table = ax.table(t, rowLabels=rows, alpha = 1, rowColours=bar_colors, colLabels=cols, cellLoc = 'center',  bbox=(0.02, 0.5, 0.3, 0.3))
    table.set_zorder(200)

    plt.show()

def _get_models_dictionary(models_list: list, instances_list: list, comparison_dict: dict, model_renames: list) -> None:
    if models_list is None:
        models_dictionary = { m: {'time': [],  'non_optimal': []} for c in instances_list for m in comparison_dict[c] }
    else:
        models_dictionary = { m: {'time': [],  'non_optimal': []} for m in models_list }
    
    for ins in instances_list:
        for m in models_dictionary:
            time_value = comparison_dict[ins][m]

            if type(time_value) == float:
                time_value = min(time_value, 300)
                non_optimal = 0

            else:
                time_value = 0
                non_optimal = 300

            for k, v in list(zip(['time', 'non_optimal'], [time_value, non_optimal])):
                models_dictionary[m][k].append(v)

    if model_renames is not None:
        for i, m in enumerate(models_list):
            models_dictionary[model_renames[i]] = models_dictionary[m]
            del models_dictionary[m]

    return models_dictionary


def _compute_statistics(models_dictionary):
    statistics_dictionary = {m:{} for m in models_dictionary}
    for m in models_dictionary:
        statistics_dictionary[m]['n_solved_instances'] = sum([not flag for flag in models_dictionary[m]['non_optimal']])
        if statistics_dictionary[m]['n_solved_instances'] == 0:
            statistics_dictionary[m]['mean_time'] = 0
        else:
            statistics_dictionary[m]['mean_time'] = sum(
                models_dictionary[m]['time']) / statistics_dictionary[m]['n_solved_instances']
    return statistics_dictionary

if __name__ == '__main__':
    main()
