import sympy as sp
from .. import utils
from ..recurrence import Recurrence

def solve(rec: Recurrence):
    print(rec.get_initial())
    print(rec.get_conditions())
    print(rec.get_transitions())
    print(rec.get_app())
    print(rec.is_linear())
    print(rec.get_all_func())
    print(rec.get_ind_var())
    print(rec.is_standard())

def solve_ultimate_periodic_linear_initial(rec: Recurrence):
    assert(rec.is_standard())

def solve_solvable_map(rec: Recurrence):
    pass
