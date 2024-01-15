import sympy as sp
from .. import utils
from ..recurrence import Recurrence

def solve(rec: Recurrence):
    solve_solvable_map(rec)

def solve_ultimate_periodic_linear_initial(rec: Recurrence):
    assert(rec.is_standard())

def solve_solvable_map(rec: Recurrence):
    transition = rec.transitions[0]
    func_decls = rec.get_all_func_decl()
    functions = [func(rec.ind_var) for func in func_decls]
    linear_parts = []
    others_parts = []
    for f_decl in func_decls:
        f_n_1 = f_decl(rec.ind_var + 1)
        linear, others = utils.split_linear_exponential_polynomial(transition[f_n_1], functions, rec.ind_var)
        linear_parts.append(linear)
        others_parts.append(others)
    matrix_linear, _ = sp.linear_eq_to_matrix(linear_parts, functions)
    print(matrix_linear)

def get_layers_for_solvable_map(rec: Recurrence):
    pass
