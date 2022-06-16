from z3 import *
from sat_utils import at_least_one, at_most_one, exactly_one, UnsatError, Vlsi_sat_abstract


class Vlsi_sat(Vlsi_sat_abstract):
    """Class for solving the VLSI problem in SAT, using the encoding 1.

    It inherits from the class `Vlsi_sat_abstract`.

    The solving procedure is the same of the encoding 0. SAT variables 'circuit_i_j_k' and 'coord_i_j_k'.
    See the `__solve` method.

    The optimization is instead improved. 
    Same structure: cycle in which at each iteration the solver is created and run from scratch.
    But now, at each iteration, the current best length of the plate (i.e. `l`) is given to the solver as upper bound for the
    length of the plate (i.e. `l_max`). (Actually, `l-1` is given as `l_max`).
    In this way, at each iteration is found a better solution with respect to the current one.
    Still no incremental solving: at each iteration, the solver is created and run from scratch. 
    See the `__optimize` method.

    """

    def __init__(self, w, n, dims, results):
        super().__init__(w, n, dims, results)


    def __solve(self, l_min, l_max):
        """Solves the given VLSI instance, using the SAT encoding 1.

        It is an auxiliary method. Its aim is to solve the VLSI instance without performing optimization: any solution is 
        good.

        Parameters
        ----------
        formulas : list of z3.z3.BoolRef, optional
            List of additional constraints to impose, by default []
        l_max : int, optional
            Maximum length of the plate, by default None.
            If None, `l_max` is computed as `sum(dimsY)`.

        Returns
        -------
        coords_sol: list of tuple of int
            List containing the coordX and coordY of the lower-left vertex of each circuit
        formula_sol: z3.z3.BoolRef
            Boolean formula containing the solution

        Raises
        ------
        UnsatError
            If the given instance is UNSAT

        Notes
        ------
        The following SAT variables are used.
        - circuit_i_j_k, where 'i' in [0,w], 'j' in [0,l_max], 'k' in [0,n].
          '(i,j)' represent two coordinates of the plate, 'k' represents a circuit.
          circuit_i_j_k is True IIF the circuit 'k' is present in the cell '(i,j)' of the plate.
        - coord_i_j_k, where 'i' in [0,w], 'j' in [0,l_max], 'k' in [0,n].
          '(i,j)' represent two coordinates of the plate, 'k' represents a circuit.
          coord_i_j_k is True IIF the left-bottom corner of the circuit 'k' is put in the cell '(i,j)' of the plate.

        """
        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

        #if l<l_min:
        #    raise UnsatError('UNSAT')

        s = Solver()  # Solver instance

        px = [[Bool(f'px_{i}_{e}') for e in range(w)] for i in range(n)]
        py = [[Bool(f'py_{i}_{f}') for f in range(l_max)] for i in range(n)]
        lr = [[Bool(f'lr_{i}_{j}') for j in range(n)] for i in range(n)]
        ud = [[Bool(f'ud_{i}_{j}') for j in range(n)] for i in range(n)]

        ph = [Bool(f'ph_{o}') for o in range(l_max-l_min+1)]
        
        #s.add( ph[l-l_min] )
        
        """for i in range(n):
            s.add( Or(px[i]) )
            s.add( Or(py[i]) )"""

        for i in range(n):
            for e in range(w-dimsX[i]):
                s.add( Or(Not(px[i][e]),px[i][e+1]) )
            for e in range(w-dimsX[i],w):
                s.add(px[i][e])
            for f in range(l_max-dimsY[i]):
                s.add( Or(Not(py[i][f]),py[i][f+1]) )
            for f in range(l_max-dimsY[i],l_max):
                s.add(py[i][f])
                
        for i in range(n):
            for j in range(i+1,n):
                s.add( Or(lr[i][j],lr[j][i],ud[i][j],ud[j][i]) )
                if w-dimsX[i]-dimsX[j] < 0:
                    s.add( Not(lr[i][j]) )
                    s.add( Not(lr[j][i]) )
                else:
                    for e in range(dimsX[i]):
                        s.add( Or(Not(lr[i][j]),Not(px[j][e])) )
                    for e in range(dimsX[j]):
                        s.add( Or(Not(lr[j][i]),Not(px[i][e])) )
                    for e in range(w-dimsX[i]-dimsX[j]+1):
                        s.add( Or(Not(lr[i][j]), px[i][e], Not(px[j][e+dimsX[i]])) )
                        s.add( Or(Not(lr[j][i]), px[j][e], Not(px[i][e+dimsX[j]])) )
                    
                """if w-dimsX[i]-dimsX[j] < 0:
                    s.add( Not(lr[j][i]) )
                else:
                    for e in range(dimsY[i]):
                        s.add( Or(Not(lr[j][i]),Not(px[i][e])) )
                    for e in range(w-dimsX[j]-dimsX[i]+1):
                        s.add( Or(Not(lr[j][i]), px[j][e], Not(px[i][e+dimsX[j]])) )"""
                    
                if l_max-dimsY[i]-dimsY[j] < 0:
                    s.add( Not(ud[i][j]) )
                    s.add( Not(ud[j][i]) )
                else:
                    for f in range(dimsY[i]):
                        s.add( Or(Not(ud[i][j]),Not(py[j][f])) )
                    for f in range(dimsY[j]):
                        s.add( Or(Not(ud[j][i]),Not(py[i][f])) )
                    for f in range(l_max-dimsY[i]-dimsY[j]+1):
                        s.add( Or(Not(ud[i][j]), py[i][f], Not(py[j][f+dimsY[i]])) )
                        s.add( Or(Not(ud[j][i]), py[j][f], Not(py[i][f+dimsY[j]])) )
                    
                """if l_max-dimsY[i]-dimsY[j] < 0:
                    s.add( Not(ud[j][i]) )
                else:
                    for f in range(dimsY[j]):
                        s.add( Or(Not(ud[j][i]),Not(py[i][f])) )
                    for f in range(l_max-dimsY[j]-dimsY[i]+1):
                        s.add( Or(Not(ud[j][i]), py[j][f], Not(py[i][f+dimsY[j]])) )"""
                    
        for i in range(n):
            for o in range(l_max-l_min+1):
                s.add( Or(Not(ph[o]),py[i][o+l_min-dimsY[i]]) )
        for o in range(l_max-l_min):
            s.add( Or(Not(ph[o]),ph[o+1]) )
                    
        """if s.check() != sat:
            raise UnsatError('UNSAT')"""
        
        return s, px, py, ph

    
    def __inject(self, s, ph, l, l_min):
        s.add( ph[l-l_min] )


    def __compute_coords(self, s, px, py, l_max):
        """Computes the length of the plate, given the coordinates of the lower-left verteces of the circuits

        Parameters
        ----------
        coords : list of tuple of int
            List containing the coordX and the coordY of the lower-left vertex of each circuit 

        Returns
        -------
        l : int
            Length of the plate
        """
        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY
        m = s.model()

        coords = []
        for i in range(n):
            for e in range(w):
                if m.evaluate(px[i][e], model_completion=True):
                    coordX = e
                    break
            for f in range(l_max):
                if m.evaluate(py[i][f], model_completion=True):
                    coordY = f
                    break
            coords.append((coordX,coordY))

        return coords


    def __optimize(self):
        """Solves the given VLSI instance, using the SAT encoding 1.

        It performs optimization: the best solution is found (if any).
        (If this class is used as a parallel process with a time limit, there is not gurantee of founding the optimal 
        solution, but only the best solution found so far).

        The implementation is based on the usage of the `__solve` method.
        Basically, a loop iterating over all the possible solutions is performed, searching for the best possible solution.
        At each iteration, the solver is created and run from scratch, with additional constraints imposing to search 
        for a solution different from the ones already found (the already found solutions are not feasible anymore) and with 
        the current best length of the plate (i.e. `l`) as upper bound for the length of the plate (i.e. `l_max`). 
        (Actually, `l-1` is given as `l_max`).

        No incremental solving: at each iteration, the solver is created and run from scratch.

        Raises
        ------
        UnsatError
            If the given instance is UNSAT

        Notes
        ------
        The solution is communicated to the user through the `results` dictionary, which is shared between the class and the 
        user. 
        Each time a better solution is found, it is injected to the `results` dictionary.
        """
        # List of additional constraints to inject
        #formulas = []
        # Boolean flag reprenting if the first solution has not been found yet

        first = True
        w, n, dimsX, dimsY = self.w, self.n, self.dimsX, self.dimsY

        areas = [dimsX[i]*dimsY[i] for i in range(n)]  # The areas of the circuits
        A_tot = sum(areas)  # The overall area of all the given circuits
        h_min = min(dimsY)  # The minimum height of a circuit
        h_max = max(dimsY)  # The maximum height of a circuit
        w_min = min(dimsX)  # The minimum width of a circuit
        w_max = max(dimsX)  # The maximum width of a circuit
        l_min = max([h_max, A_tot // w])  # The lower bound for the length
        min_rects_per_row = w // w_max  # Minimum number of circuits per row
        # max_rects_per_col = ceil(n / max([1, min_rects_per_row]))  # Maximum number of circuits per column
        #l_max =  sum(sorted(dimsY)[n-max_rects_per_col:]) 
        if min_rects_per_row==0:
            raise UnsatError('UNSAT')
        sorted_dimsY = sorted(dimsY, reverse=True)  
        if min_rects_per_row==0:
            l_max = sum(dimsY)
        else:
            l_max = sum([sorted_dimsY[i] for i in range(n) if i % min_rects_per_row == 0])  # The upper bound for the length

        s, px, py, ph = self.__solve(l_min, l_max)

        ub = l_max 
        lb = l_min 
        l = math.ceil((ub+lb)/2)        

        while lb<ub:
            #if not first:
            #    l_max = self.results['best_l']-1
            #else:
            #    l_max = self.results['best_l']-1
            if lb+1==ub:
                ub = lb    
            l = math.ceil((ub+lb)/2)
            print(lb,ub,l)

            # Search for a solution (given the additional constraints in `formulas`)
               
            s.push()
            #self.__inject(s, ph, l, l_min)
            s.add( ph[l-l_min] )

            if s.check()==sat:
                coords = self.__compute_coords(s, px, py, l_max)
                first = False
                self.results['best_coords'] = coords
                self.results['best_l'] = l
                print(l)
                ub = l
            else:
                s.pop()
                s.add( Not(ph[l-l_min]) )
                lb = l+1


                # Append into `formulas` the negation of the returned `formula`, which represents the current solution.
                # In this way, in the next iteration, the same solution is not feasible anymore
                # formulas.append(Not(formula))  

                # Length of the plate of the current solution
                """coords = self.__compute_coords(s, px, py, l_max)

                # TODO: remove
                # print(l)
                # print(coords)

                # Check if the current solution is the best solution found so far
                first = False
                self.results['best_coords'] = coords
                self.results['best_l'] = l
                print(l)
                ub = l

            except UnsatError:
                lb = l+1"""

        # The computation is finished
        self.results['finish'] = True
                
        if first:  # No solution has been found: UNSAT
            raise UnsatError('UNSAT')        


    def run(self):
        # Code executed by the process when it is runned
        try:
            self.__optimize()
        except UnsatError:
            self.results['unsat'] = True