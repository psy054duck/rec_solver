from rec_solver.core.solvable_polynomial import solve_solvable_map
from rec_solver import solve_ultimately_periodic_initial, solve_ultimately_periodic_symbolic
from rec_solver import parse_str, parse_file
from rec_solver import poly_expr_solving, solve_multivariate_rec
from rec_solver.recurrence import Recurrence, MultiRecurrence
from rec_solver import utils
import sympy as sp
import os
import logging
import sys

def test():
    # s = '''a(0) = 0; b(0) = 1; i(0) = 0; if ((a(n) < 10)) { a(n+1) = a(n) + 1; b(n+1) = b(n) - 1; i(n+1) = i(n) + 1; } else {a(n+1) = a(n) - 1; b(n+1) = b(n)*3; i(n+1) = i(n) + 1; }'''
    # s = '''a(0) = 0; b(0) = 1; i(0) = 0; if ((i(n) % 2 == 0)) { a(n+1) = a(n) + 1; b(n+1) = b(n) - 1; i(n+1) = i(n) + 1; } else {a(n+1) = a(n) - 1; b(n+1) = b(n) - 1; i(n+1) = i(n) + 1; }'''
    # s = '''a(0) = 0; b(0) = 1; if (1 == 1) { a(n+1) = a(n) + b(n)*b(n); b(n+1) = b(n) + a(n)*b(n); }'''
    # s = '''x(0) = 0; y(0) = 0; z(0) = 0; if (1 == 1) { x(n+1) = x(n) + z(n)*z(n) + 1; y(n+1) = y(n) - z(n)*z(n); z(n+1) = z(n) + (x(n) + y(n))*(x(n) + y(n)); }'''
    # s1 = '''x(0) = 0; y(0) = 0; z(0) = 0; if (true) { x(n+1) = x(n) + n; y(n+1) = y(n) + x(n); z(n+1) = z(n) + x(n)*x(n); }'''
    # s2 = '''x(0) = 0; if (true) { x(n+1) = x(n)*x(n); }'''
    # s = '''a(0) = 0; b(0) = 1; i(0) = 0; if ((a(n) < 10)) { a(n+1) = a(n) + 10; b(n+1) = b(n) - 1; i(n+1) = i(n) + 1; } else if (a(n) < 11) { a(n+1) = a(n) + 1; b(n + 1) = b(n) + 2; i(n+1) = i(n) + 1; } else {a(n+1) = a(n) - 1; b(n+1) = b(n) - 1; i(n+1) = i(n) + 1; }'''
    s = '''a(0) = a; b(0) = b; if (a(n) < 10) { a(n+1) = a(n) + 1; b(n+1) = b(n) - 1; } else { a(n + 1) = a(n) + 2; b(n + 1) = b(n) - 3; }'''
    # rec1 = parse_str(s)
    rec1 = parse_file('./examples/test7.txt')
    # closed = solve_ultimately_periodic_initial(rec1)
    # closed = solve_ultimately_periodic_symbolic(rec1)
    # closed = poly_expr_solving(rec1, 1)
    rec1.pprint()
    closed = solve_multivariate_rec(rec1)
    sp.pprint(closed)
    # print(closed.pprint())
    # rec2 = parser.parse(s2)
    # res1 = solve(rec1)
    # res2 = solve(rec2)
    # print(res1)
    # print(res2)

def test_parser():
    prefix = './examples'
    for filename in os.listdir(prefix):
        if filename.endswith('.txt'):
            print(filename)
            rec = parse_file(os.path.join(prefix, filename))
            rec.pprint()
            print('*'*100)

def test_get_terms():
    a = sp.Symbol('a', integer=True)
    f = sp.Function('f')
    e = f(a + 1) + f(a) + a + 1
    print(utils.get_terms(e))

def test_get_exponential_factor():
    n = sp.Symbol('n', integer=True)
    e = 2**n * (3**(n+1) + n*n**2) + n + 1
    e = sp.expand(sp.simplify(e))
    print(utils.get_exponential_factors(e))

def test_compression():
    seq = '1 1 1 1 1 1 1 1 1 0 1 0 1 0 1 0 1'.split()
    print(utils.compress_seq(seq))

def test_multirec():
    n = sp.Symbol('n', integer=True)
    f = sp.Function('f')
    a0 = sp.Symbol('a0', integer=True)
    a1 = sp.Symbol('a1', integer=True)
    conditions = [n <= 0, sp.Eq(n, 1), n > 1]
    recursive_calls = [{}, {}, {a0: f(n - 1), a1: f(n - 2)}]
    # post_ops = [sp.Integer(0), sp.Integer(1), a0 + a1]
    post_ops = [sp.Integer(0), sp.Integer(1), a0 + a1]
    operations = list(zip(recursive_calls, post_ops))
    branches = list(zip(conditions, operations))
    rec = MultiRecurrence(f(n), branches)
    print(rec.conditions)
    print(rec.recursive_calls)
    print(rec.post_ops)
    print(rec.func_decl)
    print(rec.is_nearly_tail())

def test_rec_sum():
    n = sp.Symbol('n', integer=True)
    m = sp.Symbol('m', integer=True)
    f = sp.Function('f')
    a0 = sp.Symbol('a0', integer=True)
    conditions = [n <= 0, n > 0]
    # recursive_calls = [{}, {a0: f(n - 1)}]
    # post_ops = [sp.Integer(0), a0 + 1]
    transitions = [{f(n, m): n + m}, {f(n, m): f(n - 1, m + 1)}]
    recursive_calls = [{}, {a0: f(n - 1, m + 1)}]
    post_ops = [(n + m,), (a0,)]
    operations = list(zip(recursive_calls, post_ops))
    branches = list(zip(conditions, operations))
    # rec = MultiRecurrence(branches)
    rec = MultiRecurrence(f(n, m), conditions, transitions, recursive_calls, post_ops)
    closed_forms = solve_multivariate_rec(rec)
    for closed_form in closed_forms:
        sp.pprint(closed_form)

def test_multirec():
    logging.basicConfig(level=logging.DEBUG, stream=sys.stdout)
    rec = parse_file('./examples/test8.txt')
    rec.pprint()
    solve_multivariate_rec(rec)


if __name__ == '__main__':
    # test_multirec()
    # test_parser()
    test_rec_sum()
    # test()
    # test_get_terms()
    # test_get_exponential_factor()
    # test_compression()