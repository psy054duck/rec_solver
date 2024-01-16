from src.core.solvable_polynomial import solve
from src.rec_parser import parser
from src import utils
import sympy as sp

def test():
    s = '''a(0) = 0; b(0) = 1; if ((a(n) < 100)) { a(n+1) = a(n) + 1; b(n+1) = b(n) - 1; } else {a(n+1) = a(n) - 1; b(n+1) = b(n) - 1; }'''
    # s = '''a(0) = 0; b(0) = 1; if (1 == 1) { a(n+1) = a(n) + b(n)*b(n); b(n+1) = b(n) + a(n)*b(n); }'''
    # s = '''x(0) = 0; y(0) = 0; z(0) = 0; if (1 == 1) { x(n+1) = x(n) + z(n)*z(n) + 1; y(n+1) = y(n) - z(n)*z(n); z(n+1) = z(n) + (x(n) + y(n))*(x(n) + y(n)); }'''
    # s1 = '''x(0) = 0; y(0) = 0; z(0) = 0; if (true) { x(n+1) = x(n) + n; y(n+1) = y(n) + x(n); z(n+1) = z(n) + x(n)*x(n); }'''
    # s2 = '''x(0) = 0; if (true) { x(n+1) = x(n)*x(n); }'''
    rec1 = parser.parse(s)
    # rec2 = parser.parse(s2)
    res1 = solve(rec1)
    # res2 = solve(rec2)
    print(res1)
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

if __name__ == '__main__':
    test()
    # test_get_terms()
    # test_get_exponential_factor()