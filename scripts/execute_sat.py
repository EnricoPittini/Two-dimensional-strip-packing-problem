import argparse
import sys
import os

import importlib

import time

import utils
#python scripts\execute_sat.py sat\encoding_2.py minizinc\instances\ins-10.txt 300

# TODO: remove
"""
import threading

class myThread(threading.Thread):
    def __init__(self, w, n, dims, encoding_module):
        threading.Thread.__init__(self)
        self.w = w
        self.n = n
        self.dims = dims
        self.vlsi_sat = encoding_module.vlsi_sat
        self.UnsatError = encoding_module.UnsatError  # TODO refactor
    def run(self):
        try:
            self.coords, self.l = self.vlsi_sat(self.w, self.n, self.dims)
            self.unsat = False
        except self.UnsatError:
            self.unsat = True
    def get_id(self): 
        # returns id of the respective thread
        if hasattr(self, '_thread_id'):
            return self._thread_id
        for id, thread in threading._active.items():
            if thread is self:
                return id
    def raise_exception(self):
        thread_id = self.get_id()
        res = ctypes.pythonapi.PyThreadState_SetAsyncExc(thread_id,
              ctypes.py_object(SystemExit))
        if res > 1:
            ctypes.pythonapi.PyThreadState_SetAsyncExc(thread_id, 0)
            print('Exception raise failure')"""
      

def main():
    parser = argparse.ArgumentParser(description='Script for executing a VLSI SAT encoding.')

    parser.add_argument('encoding-path', type=str, help='The encoding to execute.')

    parser.add_argument('instance-path', type=argparse.FileType('r', encoding='UTF-8'), help='The instance to solve.')

    parser.add_argument('time-limit', type=int, default=300, nargs='?', help='Time limit, in seconds')

    parser.add_argument('output-folder-path', type=str, default=os.getcwd(), nargs='?', 
                        help='The path in which the output file is stored.')

    parser.add_argument('--no-create-output', action='store_true', 
                        help='Skip the creation of the output solution.')

    parser.add_argument('--no-visualize-output', action='store_true', 
                        help='Skip the visualization of the output solution (defaults as true if `--no-create-output` ' + \
                        'is passed).')

    arguments = parser.parse_args()

    instance_file = vars(arguments)['instance-path']
    w, n, dims = utils.parse_instance_txt(instance_file)
    w = int(w)
    n = int(n)
    dims = [(int(dims[i][0]),int(dims[i][1])) for i in range(n)]

    encoding_path = vars(arguments)['encoding-path']
    encoding_abspath = os.path.abspath(encoding_path)
    module_name = os.path.basename(encoding_path).split('.')[0]
    sys.path.insert(1, os.path.join(os.path.dirname(__file__), os.path.dirname(encoding_abspath)))
    encoding_module = importlib.import_module(module_name)
    vlsi_sat = encoding_module.vlsi_sat
    UnsatError = encoding_module.UnsatError  # TODO refactor

    try:
        start_time = time.time()
        coords, l = vlsi_sat(w, n, dims, timeout=vars(arguments)['time-limit'])
        solving_time = time.time() - start_time
        coordsX = [coords[i][0] for i in range(n)]
        coordsY = [coords[i][1] for i in range(n)]
        print(solving_time)
    except UnsatError:
        sys.exit('UNSAT')

    """# TODO: remove
    start_time = time.time()
    coords, l = vlsi_sat(w, n, dims)
    # thr = myThread(w, n, dims, encoding_module)
    # thr.start()
    # thr.join(float(vars(arguments)['time-limit']))
    solving_time = time.time() - start_time

    if thr.is_alive():
        thr.raise_exception()
        sys.exit('Time limit exceeded')

    if thr.unsat:
        sys.exit('UNSAT')

    coords, l = thr.coords, thr.l
    coordsX = [coords[i][0] for i in range(n)]
    coordsY = [coords[i][1] for i in range(n)]
    print(solving_time)"""

    if not arguments.no_create_output:
        output_folder_path = vars(arguments)['output-folder-path']

        instance_file_name = os.path.basename(instance_file.name)
        output_file = os.path.join(output_folder_path,f'solution-{instance_file_name}')#f'{output_folder_path}\\solution-{instance_file.name.split("/")[-1]}'

        try:
            utils.create_output_file(output_file, w, n, dims, l, coordsX, coordsY)
        except FileNotFoundError as e:
            #print(e) 
            sys.exit(f'Output path {output_folder_path} does not exist.')
    
        if not arguments.no_visualize_output:
            scripts_folder = os.path.dirname(sys.argv[0])
            visualize_script_path = os.path.join(scripts_folder,'visualize.py')
            print(output_file)
            os.system(f'python {visualize_script_path} "{output_file}"')


if __name__ == "__main__":
    main()