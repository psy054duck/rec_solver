import sympy as sp
from .. import utils
from ..recurrence import Recurrence
from functools import reduce

def solve_solvable_map(rec: Recurrence):
    components = get_layers_for_solvable_map(rec)
    for component in components:
        partial_closed_form = solve_solvable_map_for_component(rec, component)
        partial_closed_form = {k: c.subs(rec.initial, simultaneous=True) for k, c in partial_closed_form.items()}
        rec.simplify_with_partial_solution(partial_closed_form)
    return rec.closed_forms

def solve_solvable_map_for_component(rec: Recurrence, component):
    ordered_component = list(component)
    transition = rec.transitions[0]
    func_decls = [function.func for function in ordered_component]
    keys = [func(rec.ind_var + 1) for func in func_decls]
    linear_parts = []
    other_parts = []
    for k in keys:
        expr = transition[k]
        linear, other = utils.split_linear_others(expr, ordered_component, rec.ind_var)
        linear_parts.append(linear)
        other_parts.append(other)
    linear_matrix_form, _ = sp.linear_eq_to_matrix(linear_parts, ordered_component)
    matrix_eigenvals = linear_matrix_form.eigenvals()
    base_multiplicity_other_part = [utils.get_exponential_base_and_multiplicity(other, rec.ind_var) for other in other_parts]
    all_bases = set(matrix_eigenvals) | reduce(set.union, (set(base_mul.keys()) for base_mul in base_multiplicity_other_part), set())
    bases_multi_dict = {base: 0 for base in all_bases}
    for base in all_bases:
        for cur_dict in [matrix_eigenvals] + base_multiplicity_other_part:
            bases_multi_dict[base] += cur_dict.get(base, 0)
    n = sum(bases_multi_dict.values())
    first_n_values, _ = rec.get_first_n_values(n)
    eps = solve_for_exponential_polynomial(bases_multi_dict, func_decls, first_n_values, rec.ind_var)
    return eps

def solve_for_exponential_polynomial(bases_multi_dict, func_decls, first_n_values, ind_var):
    template, coeffs = gen_exponential_polynomials_template(bases_multi_dict, ind_var)
    eps = {}
    for func in func_decls:
        eqs = []
        for i, value in enumerate(first_n_values):
            cur_func_value = value[func(i)]
            eqs.append(cur_func_value - template.subs(ind_var, i))
        sol = sp.solve(eqs, coeffs)
        instantiated_ep = template.subs(sol)
        eps[func(ind_var)] = instantiated_ep
    return eps

def gen_exponential_polynomials_template(bases_multi_dict, ind_var):
    template = sp.Integer(0)
    unknowns = []
    for base, multi in bases_multi_dict.items():
        poly_template, coeffs = gen_polynomial_template_for_degree(ind_var, multi-1, str(base))
        if base == 0:
            template += poly_template*sp.Piecewise((1, sp.Eq(ind_var, 0)), (0, True))
        else:
            template += poly_template*base**ind_var
        unknowns.extend(coeffs)
    return template, unknowns

def gen_polynomial_template_for_degree(ind_var, degr, name=""):
    # coeffs = sp.symbols('_%s_c:%d' % (name, degr + 1))
    coeffs = [sp.Symbol('_%s_c%d' % (name, i)) for i in range(degr + 1)]
    template = sum([c*ind_var**i for i, c in enumerate(coeffs)])
    return template, list(coeffs)

def get_layers_for_solvable_map(rec: Recurrence):
    # digraph, functions = build_adjacency_matrix(rec)
    # components = utils.sorted_strong_ly_connected_components(digraph)
    # return [{functions[i] for i in component} for component in components]
    components = []
    transition = rec.transitions[0]
    functions = [func(rec.ind_var) for func in rec.func_decls]
    considered = []
    while set(considered) != set(functions):
        cur_considered = []
        considered_yet = set(functions) - set(considered)
        for func in considered_yet:
            func_next = func.subs({rec.ind_var: rec.ind_var + 1})
            liner_part, poly_part = utils.split_linear_others(transition[func_next], functions, rec.ind_var)
            all_apps = utils.get_app(poly_part)
            if all_apps.issubset(set(considered)):
                cur_considered.append(func)
        digraph = build_adjacency_matrix(rec, cur_considered)
        cs = utils.sorted_strong_ly_connected_components(digraph)
        for c in cs:
            components.append([cur_considered[i] for i in c])
            considered.extend(components[-1])
    return components
        # considered.extend(cur_considered)

def build_adjacency_matrix(rec: Recurrence, projection):
    transition = rec.transitions[0]
    digraph = sp.zeros(len(rec.func_decls))
    functions = [func(rec.ind_var) for func in rec.func_decls]
    for i, f_i in enumerate(projection):
        f_n_1 = f_i.subs({rec.ind_var: rec.ind_var + 1})
        # _, other_expr = utils.split_linear_others(transition[f_n_1], functions, rec.ind_var)
        for j, f_j in enumerate(projection):
            # if f_j.func in utils.get_func_decls(other_expr):
            if f_j.func in utils.get_func_decls(transition[f_n_1]):
                digraph[i, j] = 1
    return digraph

def is_solvable_map(rec: Recurrence):
    conditions = rec.conditions
    if conditions[0].simplify() != sp.true: return False
    ind_var = rec.ind_var
    func_decls = rec.func_decls
    if any((list(func.nargs)[0] > 1 for func in func_decls)): return False
    layers = get_layers_for_solvable_map(rec)
    transition = rec.transitions[0]
    functions = [func_decl(ind_var) for func_decl in rec.func_decls]
    for i, layer in enumerate(layers):
        functions_later_layers = reduce(set.union, layers[i:], set())
        for func in layer:
            f_n_1 = func.func(ind_var + 1)
            _, other_expr = utils.split_linear_others(transition[f_n_1], functions, ind_var)
            apps = utils.get_app(other_expr) - {ind_var}
            if any((app in functions_later_layers for app in apps)):
                return False
    return True