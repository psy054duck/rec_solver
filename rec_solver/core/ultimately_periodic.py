import sympy as sp
from .. import utils
from ..recurrence import Recurrence
from ..closed_form import PeriodicClosedForm, PiecewiseClosedForm
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
    closed_form = PiecewiseClosedForm()
    while n < bnd:
        n *= 2
        candidate, guessed_index_seq = _compute_candidate_solution(rec, start, n, ith)
        print(candidate)
        smallest = verify(rec, candidate, guessed_index_seq)
        shift_candidate = candidate.subs({rec.ind_var: rec.ind_var - start})
        closed_form = closed_form.concatenate(shift_candidate)
        if smallest >= 0: # means hypothesis is wrong
            start = smallest
        else:
            break
        ith += 1
    print(closed_form)

def verify(rec: Recurrence, candidate_sol: PiecewiseClosedForm, pattern: list):
    conditions = rec.conditions
    transitions = rec.transitions
    start = sum([cnt for _, cnt in pattern[:-1]])
    last_closed_form = candidate_sol.closed_forms[-1]
    assert(isinstance(last_closed_form, PeriodicClosedForm))
    period = last_closed_form.period
    periodic_index_seq, _ = pattern[-1]
    n = sp.Symbol('n', integer=True)
    k = sp.Symbol('k', integer=True)
    n_range = n >= start
    for r, i in enumerate(periodic_index_seq):
        cond = conditions[i]
        cond = cond.subs(last_closed_form.get_rth_part_closed_form(r), simultaneous=True)
        cond = cond.subs({candidate_sol.ind_var: period*k + r})
        cond_range = cond.as_set()
        k_range = n_range.subs({n: period*k + r}).as_set()
        if not k_range.is_subset(cond_range):
            smallest = _smallest_violation(k_range, cond_range)
            smallest = (smallest - r)/period
            return smallest
    return -1

def _smallest_violation(n_range: sp.Interval, cond_range: sp.Interval):
    comp_cond_range = cond_range.complement(sp.Reals)
    intersect = n_range.intersect(comp_cond_range)
    left = intersect.inf
    if not intersect.contains(left):
        left += 1
    return left


def _compute_candidate_solution(rec: Recurrence, start, n, ith):
    values, index_seq = rec.get_n_values_starts_with(start, n)
    compressed_seq = utils.compress_seq(index_seq)
    guessed_patterns = [seq for seq, _ in compressed_seq]
    thresholds = [0] + [cnt for _, cnt in compressed_seq[:-1]]
    nonconditional = [_solve_as_nonconditional(rec, pattern) for pattern in guessed_patterns]
    initials = [values[i] for i in thresholds]
    debug_prefix = "%dth guess: " % ith
    padding = " "*len(debug_prefix)
    logger.debug(debug_prefix + "values are %s" % values)
    logger.debug(padding + "prefix of index sequence is %s" % index_seq)
    logger.debug(padding + "the guessed patterns are %s" % guessed_patterns)
    # print(nonconditional)
    closed_forms = []
    for initial, closed, threshold in zip(initials, nonconditional, thresholds):
        mapping = {func(0): initial[func(start + threshold)] for func in rec.func_decls} | {rec.ind_var: rec.ind_var - threshold}
        closed_forms.append(closed.subs(mapping))
    return PiecewiseClosedForm(thresholds, closed_forms, rec.ind_var), compressed_seq

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
