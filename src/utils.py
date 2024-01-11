import sympy as sp
from functools import reduce

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