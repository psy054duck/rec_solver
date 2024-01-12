from src.core.solver import solve
from src.rec_parser import parser
from src import utils
import sympy as sp

def test():
    s = '''a(0) = 0; b(0) = 1; if ((a(n) < 100)) { a(n+1) = a(n) + 1; b(n+1) = b(n) - 1; } else {a(n+1) = a(n) - 1; b(n+1) = b(n) - 1; }'''
    rec = parser.parse(s)
    solve(rec)

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