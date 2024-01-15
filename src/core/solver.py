import sympy as sp
from .. import utils
from ..recurrence import Recurrence
from functools import reduce

def solve(rec: Recurrence):
    solve_solvable_map(rec)

def solve_ultimate_periodic_linear_initial(rec: Recurrence):
    assert(rec.is_standard())

def solve_solvable_map(rec: Recurrence):
    transition = rec.transitions[0]
    func_decls = rec.func_decls
    functions = [func(rec.ind_var) for func in func_decls]
    components = get_layers_for_solvable_map(rec)
    for component in components:
        solve_solvable_map_for_component(rec, component)

def solve_solvable_map_for_component(rec: Recurrence, component):
    ordered_component = list(component)
    transition = rec.transitions[0]
    keys = [function.func(rec.ind_var + 1) for function in ordered_component]
    linear_parts = []
    other_parts = []
    for k in keys:
        expr = transition[k]
        linear, other = utils.split_linear_others(expr, ordered_component, rec.ind_var)
        linear_parts.append(linear)
        other_parts.append(other)
    linear_matrix_form, _ = sp.linear_eq_to_matrix(linear, ordered_component)
    matrix_eigenvals = linear_matrix_form.eigenvals()
    base_multiplicity_other_part = [utils.get_exponential_base_and_multiplicity(other, rec.ind_var) for other in other_parts]
    all_bases = set(matrix_eigenvals) | reduce(set.union, (set(base_mul.keys()) for base_mul in base_multiplicity_other_part), set())
    bases_multi_dict = {}
    for base in all_bases:
        for cur_dict in [matrix_eigenvals] + base_multiplicity_other_part:
            bases_multi_dict.setdefault(base, -1)
            bases_multi_dict[base] += cur_dict.get(base, 0)

def get_layers_for_solvable_map(rec: Recurrence):
    digraph, functions = build_adjacency_matrix(rec)
    components = utils.sorted_strong_ly_connected_components(digraph)
    return [{functions[i] for i in component} for component in components]

def build_adjacency_matrix(rec: Recurrence):
    transition = rec.transitions[0]
    digraph = sp.zeros(len(rec.func_decls))
    functions = [func(rec.ind_var) for func in rec.func_decls]
    for i, f_decl in enumerate(rec.func_decls):
        f_n_1 = f_decl(rec.ind_var + 1)
        _, other_expr = utils.split_linear_others(transition[f_n_1], functions, rec.ind_var)
        for j, f_decl_j in enumerate(rec.func_decls):
            if f_decl_j in utils.get_func_decls(other_expr):
                digraph[i, j] = 1
    return digraph, functions
