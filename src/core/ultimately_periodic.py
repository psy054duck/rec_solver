import sympy as sp
from .. import utils
from ..recurrence import Recurrence
from functools import reduce

def solve_ultimately_periodic_initial(rec: Recurrence):
    assert(rec.is_all_initialized())
    n = 1
    while True:
        n *= 2
        _, index_seq = rec.get_first_n_values(n)
        pattern = guess_pattern_from_seq(index_seq)

def guess_pattern_from_seq(seq):
    pass
