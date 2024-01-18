import sympy as sp
from .. import utils
from ..recurrence import Recurrence
from functools import reduce
from .solvable_polynomial import solve_solvable_map

def solve_ultimately_periodic_initial(rec: Recurrence, bnd=100):
    assert(rec.is_all_initialized())
    n = 1
    while n < bnd:
        n *= 2
        values, index_seq = rec.get_first_n_values(n)
        compressed_seq = utils.compress_seq(index_seq)
        print(compressed_seq)
        closed_forms = [_solve_as_nonconditional(rec, seq) for seq, _ in compressed_seq]
        print(closed_forms)

def _solve_as_nonconditional(rec: Recurrence, seq):
    new_rec = Recurrence.build_nonconditional_from_rec_by_seq(rec, seq, {})
    closed_form = solve_solvable_map(new_rec)
    return closed_form
