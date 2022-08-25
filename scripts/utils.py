import io
import os


MINIZINC_ERRORS = ['UNSATISFIABLE', 'UNBOUNDED', 'UNSATorUNBOUNDED', 'UNKNOWN', 'ERROR']

GECODE_MODELS = [f'model_6{i}' for i in 'FG']
CHUFFED_MODELS = [f'model_{i}' for i in range(3)] + [f'model_3{i}' for i in 'ABC'] + [f'model_4A{i}' for i in range(8)] +\
    [f'model_4{i}{j}' for i in 'BC' for j in range(3)] + ['model_5'] + [f'model_6{i}' for i in 'ABC'] +\
    [f'model_6{i}{j}' for i in 'DE' for j in range(2)]
CHUFFED_ROTATION_MODELS = ['model_r_0'] + [f'model_r_1{i}' for i in 'ABCD'] +\
    [f'model_r_{i}{j}' for i in [2, 3] for j in 'AB'] + [f'model_r_4{i}' for i in 'ABCDEFGH'] +\
    [f'model_r_5{i}' for i in 'CEH'] + [f'model_r_7{i}' for i in 'ABCDEFG']
MINIZINC_MODELS = GECODE_MODELS + CHUFFED_MODELS + CHUFFED_ROTATION_MODELS

SAT_ENCODINGS = [f'encoding_{i}' for i in range(4)] + [f'encoding_{4}{i}' for i in ['A', 'B', 'C', 'D', 'E', 'F']] +\
    ['encoding_5'] + ['encoding_6A', 'encoding_6B'] + [f'encoding_{7}{i}' for i in ['A', 'B', 'C', 'D']] +\
        [f'encoding_{8}{i}' for i in ['A', 'B', 'C', 'D', 'E']] +  [f'encoding_{9}{i}' for i in ['A', 'B', 'AA', 'AD', 'BA', 'BD']] +\
             ['encoding_10A', 'encoding_10B', 'encoding_10C'] + ['encoding_11', 'encoding_11A', 'encoding_11B', 'encoding_11C']
SAT_ROTATION_ENCODINGS = ['encoding_11', 'encoding_11A', 'encoding_11B', 'encoding_11C']

SMT_ENCODINGS = [f'encoding_{i}' for i in range(2)] + [f'encoding_{2}{i}' for i in ['A', 'B', 'C']] +\
     [f'encoding_{3}{i}' for i in ['A', 'B', 'C', 'D', 'E', 'F']] + [f'encoding_{4}{i}' for i in ['A', 'B', 'C', 'D', 'E', 'F']] +\
        ['encoding_5A', 'encoding_5B']
SMT_ROTATION_ENCODINGS = ['encoding_5A', 'encoding_5B']
SMT_IMPOSED_LOGIC_ENCODINGS = [f'encoding_{3}{i}' for i in ['A', 'B', 'C', 'D', 'E', 'F']] + [f'encoding_{4}{i}' for i in ['A', 'B', 'C', 'D', 'E', 'F']]
SMT_SOLVERS = ['z3', 'cvc5', 'yices-smt2']

AMPL_SOLVER_CHOICES = ['cbc','cplex','gurobi']
AMPL_MODEL_CHOICES = ['model_0','model_1', 'model_2', 'model_r_0', 'model_grid', 'model_r_grid']

INSTANCES = [f'ins-{i}' for i in range(1,41)] + ['ins-unsat']

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
    os.makedirs(os.path.dirname(output_file), exist_ok=True)
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
