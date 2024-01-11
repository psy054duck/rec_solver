import sympy as sp
from .. import utils
from ..recurrence import Recurrence

def solve(rec: Recurrence, n):
    print(rec.get_conditions())
    print(rec.get_transitions())
