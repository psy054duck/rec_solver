import sympy as sp
from .. import utils
from ..recurrence import Recurrence
from functools import reduce
from .solvable_polynomial import solve_solvable_map

def solve_ultimately_periodic_initial(rec: Recurrence, bnd=100):
    assert(rec.is_all_initialized())
    n = 1
    start = 0
    while n < bnd:
        n *= 2
        values, index_seq = rec.get_n_values_starts_with(start, n)
        compressed_seq = utils.compress_seq(index_seq)
        guessed_patterns = [seq for seq, _ in compressed_seq]
        pattern_cnt = [cnt for _, cnt in compressed_seq[:-1]]
        nonconditional = [_solve_as_nonconditional(rec, pattern) for pattern in guessed_patterns]
        initials = [values[0]] + [values[i] for i in pattern_cnt]
        print(initials)

def _solve_as_nonconditional(rec: Recurrence, seq):
    new_rec = Recurrence.build_nonconditional_from_rec_by_seq(rec, seq, {})
    closed_form = solve_solvable_map(new_rec)
    return closed_form

def _apply_initial_values(closed_form, initial):
    return {k: v.subs(initial, simultaneous=True) for k, v in closed_form.items()}
