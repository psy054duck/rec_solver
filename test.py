from rec_solver.core.solvable_polynomial import solve_solvable_map
from rec_solver import solve_ultimately_periodic_initial, solve_ultimately_periodic_symbolic
from rec_solver import parse_str, parse_file
from rec_solver.core.poly_expr import poly_expr_solving
from rec_solver.recurrence import Recurrence
from rec_solver import utils
import sympy as sp

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
    rec1 = parse_file('./examples/test2.txt')
    # closed = solve_ultimately_periodic_initial(rec1)
    # closed = solve_ultimately_periodic_symbolic(rec1)
    poly_expr_solving(rec1, 1)
    # print(closed)
    # print(closed.to_z3())
    # rec2 = parser.parse(s2)
    # res1 = solve(rec1)
    # res2 = solve(rec2)
    # print(res1)
    # print(res2)

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

if __name__ == '__main__':
    test()
    # test_get_terms()
    # test_get_exponential_factor()
    # test_compression()