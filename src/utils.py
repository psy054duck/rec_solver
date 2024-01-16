import sympy as sp
from functools import reduce
import networkx as nx
import numpy as np

def is_linear(expr, terms):
    '''Check whether "expr" is linear in terms of "terms"'''
    for x in terms:
        for y in terms:
            try: 
                if not sp.Eq(sp.diff(expr, x, y), 0):
                    return False
            except TypeError:
                return False
    return True

def get_app(expr):
    '''Get applications (with symbolic arguments) and symbols from "expr"'''
    try:
        args = expr.args
    except:
        args = set()
    if expr.is_number:
        return set()
    if (expr.func.is_Function and not any(arg.is_number for arg in args)) or expr.is_Symbol:
        return {expr}
    return reduce(set.union, [get_app(arg) for arg in args], set())

def get_func_decls(expr):
    apps = get_app(expr)
    return {app.func for app in apps if not app.is_number}

def get_exponential_base_and_multiplicity(expr, ind_var):
    res = {}
    factors = _get_exponential_factors(expr, ind_var)
    factors_part = sp.Integer(0)
    for factor in factors:
        coeff = expr.coeff(factor)
        coeff_poly = coeff.as_poly([ind_var])
        res[factor.args[0]] = coeff_poly.total_degree() + 1
        factors_part = factors_part + expr.coeff(factor)*factor
    rest = sp.simplify(expr - factors_part).as_poly([ind_var])
    res[sp.Integer(1)] = rest.total_degree() + 1
    return res

def _get_exponential_factors(expr, ind_var):
    if expr.is_number:
        return set()
    if expr.is_Pow and expr.args[0].is_number and ind_var in expr.args[1].free_symbols:
        return {expr}
    return reduce(set.union, (_get_exponential_factors(arg, ind_var) for arg in expr.args), set())

def split_linear_others(expr, functions, ind_var):
    '''For an expression of form Ax(n) + others, return (Ax(n), others)'''
    expr = sp.expand(expr)
    linear_part = sp.Integer(0)
    for f in functions:
        expr_poly = expr.as_poly(functions)
        coeff = expr_poly.coeff_monomial(f)
        linear_part = linear_part + coeff*f
    ep = sp.simplify(expr - linear_part)
    return linear_part, ep

def sorted_strong_ly_connected_components(matrix):
    G = nx.DiGraph(np.array(matrix.tolist(), dtype=int))
    # components = list(nx.strongly_connected_components(G))
    condensed = nx.condensation(G)
    sorted_condensed = list(reversed(list(nx.topological_sort(condensed))))
    components = [condensed.nodes.data()[i]['members'] for i in sorted_condensed]
    return components
