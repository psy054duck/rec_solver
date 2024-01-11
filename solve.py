from src.core.solver import solve
from src.rec_parser import parser
import sympy as sp

def test():
    s = '''a = 0; b = 1; if ((a < 100)) { a = a + 1; b = b - 1; } else {a = a - 1; b = b - 1; }'''
    rec = parser.parse(s)
    n = sp.Symbol('n', integer=True)
    solve(rec, n)

if __name__ == '__main__':
    test()