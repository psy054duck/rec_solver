import sympy as sp
from .. import utils
from ..recurrence import Recurrence
from ..closed_form import PeriodicClosedForm
from functools import reduce
from .solvable_polynomial import solve_solvable_map, is_solvable_map
import logging

logger = logging.getLogger(__name__)

class UnsolvableError(Exception):
    pass

def solve_ultimately_periodic_initial(rec: Recurrence, bnd=100):
    assert(rec.is_all_initialized())
    n = 1
    start = 0
    ith = 1
    partial_closed_form = []
    while n < bnd:
        n *= 2
        values, index_seq = rec.get_n_values_starts_with(start, n)
        compressed_seq = utils.compress_seq(index_seq)
        guessed_patterns = [seq for seq, _ in compressed_seq]
        pattern_cnt = [0] + [cnt for _, cnt in compressed_seq[:-1]]
        nonconditional = [_solve_as_nonconditional(rec, pattern) for pattern in guessed_patterns]
        initials = [values[i] for i in pattern_cnt]
        debug_prefix = "%dth guess: " % ith
        logger.debug(debug_prefix + "prefix of index sequence is %s" % index_seq)
        logger.debug(" "*len(debug_prefix) + "the guessed patterns are %s" % guessed_patterns)
        # print(nonconditional)
        for initial, closed, threshold in zip(initials, nonconditional, pattern_cnt):
            mapping = {func(0): initial[func(threshold)] for func in rec.func_decls}
        ith += 1

def _solve_as_nonconditional(rec: Recurrence, seq):
    new_rec = Recurrence.build_nonconditional_from_rec_by_seq(rec, seq, {})
    period = len(seq)
    if is_solvable_map(new_rec):
        closed_form = []
        raw_closed_form = solve_solvable_map(new_rec)
        # modulo part
        for i in range(period):
            shift_closed = {v: c.subs({rec.ind_var: (rec.ind_var - i)/period}, simultaneous=True) for v, c in raw_closed_form.items()}
            for j in seq[:i]:
                shift_closed = rec.run_one_iteration_for_ith_transition(shift_closed, j)
            closed_form.append(shift_closed)
        res = PeriodicClosedForm(closed_form, rec.ind_var)
    else:
        raise UnsolvableError("Recurrence of this kind is not solvable.")
    return res

def _apply_initial_values(closed_form, initial):
    return {k: v.subs(initial, simultaneous=True) for k, v in closed_form.items()}
