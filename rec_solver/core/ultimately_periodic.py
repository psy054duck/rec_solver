import sympy as sp
import logging
# import cvc5.pythonic as z3
import z3
from functools import reduce

from .. import utils
from ..recurrence import Recurrence
from ..closed_form import PeriodicClosedForm, PiecewiseClosedForm, SymbolicClosedForm
from .solvable_polynomial import solve_solvable_map, is_solvable_map

logger = logging.getLogger(__name__)

class UnsolvableError(Exception):
    pass

def solve_ultimately_periodic_symbolic(rec: Recurrence, bnd=100, precondition=z3.BoolVal(True)):
    z3_solver = z3.Solver()
    z3_solver.add(precondition)
    acc_condition = z3.BoolVal(True)
    i = 0
    logger.debug("Solving recurrence %s" % rec)
    constraints = []
    closed_forms = []
    while z3_solver.check(acc_condition) != z3.unsat:
        i += 1
        model = z3_solver.model()
        parameters = rec.get_symbolic_values()
        cur_val = {p: model.eval(utils.to_z3(p), model_completion=True).as_long() for p in parameters}
        initialized_rec = rec.subs(cur_val)
        _, index_seq = _solve_ultimately_periodic_initial(initialized_rec)
        # qs = [z3.Int('q%d' % i) for i in range(len(index_seq) - 1)]
        qs = sp.symbols('q:%d' % (len(index_seq) - 1))
        index_seq_temp = [(s[0], q) for s, q in zip(index_seq, qs)] + [index_seq[-1]]
        can_sol = _compute_solution_by_index_seq(rec, index_seq_temp)
        constraint, k = _set_up_constraints(rec, can_sol, index_seq_temp)
        constraint = z3.And(constraint, *[utils.to_z3(q) >= 1 for q in qs])
        logger.debug('In the %dth iteration: the set up index sequence template is %s' % (i, index_seq_temp))
        logger.debug('In the %dth iteration: the closed-form solution is\n%s' % (i, can_sol))
        logger.debug('In the %dth iteration: the set up constraint is\n%s' % (i, constraint))
        q_linear = [utils.compute_q(constraint, q, parameters, k) for q in qs]
        constraint_no_q = z3.substitute(constraint, *[(utils.to_z3(q), linear) for q, linear in zip(qs, q_linear)])
        qe = z3.Tactic('qe')
        constraint_no_kq = z3.simplify(z3.And(*qe.apply(z3.ForAll(k, z3.Implies(k >= 0, constraint_no_q)))[0]))
        logger.debug('In the %dth iteration: the parameters satisfy\n%s' % (i, constraint_no_kq))
        acc_condition = z3.And(acc_condition, z3.Not(constraint_no_kq))
        constraints.append(constraint_no_kq)
        mapping = {q: sp.sympify(str(linear)) for q, linear in zip(qs, q_linear)}
        closed_forms.append(can_sol.simple_subs(mapping))
    return SymbolicClosedForm(constraints, closed_forms)

def solve_ultimately_periodic_initial(rec: Recurrence, bnd=100):
    closed_form, _ = _solve_ultimately_periodic_initial(rec, bnd)
    return closed_form

def _solve_ultimately_periodic_initial(rec: Recurrence, bnd=100):
    assert(rec.is_all_initialized())
    n = 1
    start = 0
    ith = 1
    closed_form = PiecewiseClosedForm()
    acc_index_seq = []
    while n < bnd:
        n *= 2
        candidate, guessed_index_seq = _compute_candidate_solution(rec, start, n, ith)
        acc_index_seq.extend(guessed_index_seq)
        smallest = verify(rec, candidate, guessed_index_seq)
        shift_candidate = candidate.subs({candidate.ind_var: candidate.ind_var - start})
        closed_form = closed_form.concatenate(shift_candidate)
        if smallest is not sp.oo: # means hypothesis is wrong
            start = smallest
        else:
            break
        ith += 1
    return closed_form, acc_index_seq

def verify(rec: Recurrence, candidate_sol: PiecewiseClosedForm, pattern: list):
    conditions = rec.conditions
    start = sum([cnt for _, cnt in pattern[:-1]])
    last_closed_form = candidate_sol.closed_forms[-1]
    assert(isinstance(last_closed_form, PeriodicClosedForm))
    period = last_closed_form.period
    periodic_index_seq, _ = pattern[-1]
    n = sp.Symbol('n', integer=True)
    k = sp.Symbol('k', integer=True)
    n_range = n >= start
    smallest = sp.oo
    for r, i in enumerate(periodic_index_seq):
        cond = conditions[i]
        cond = cond.subs(last_closed_form.get_rth_part_closed_form(r), simultaneous=True)
        cond = cond.subs({candidate_sol.ind_var: period*k + r}, simultaneous=True)
        cond_range = cond.as_set()
        k_range = n_range.subs({n: period*k + r}, simultaneous=True).as_set()
        if not k_range.is_subset(cond_range):
            cur_smallest = _smallest_violation(k_range, cond_range, period, r, rec.ind_var)
            cur_smallest = cur_smallest*period + r
            smallest = min(smallest, cur_smallest)
    return smallest

def _smallest_violation(n_range: sp.Interval, cond_range: sp.Interval, period, r, ind_var):
    intersect = n_range.intersect(cond_range)
    comp = intersect.complement(n_range)
    left = sp.ceiling(comp.inf)
    if not comp.contains(left):
        left += 1
    return left

def _compute_solution_by_index_seq(rec: Recurrence, index_seq):
    patterns = [seq for seq, _ in index_seq]
    thresholds = [0] + [cnt for _, cnt in index_seq[:-1]] + [sp.oo]
    nonconditional = [_solve_as_nonconditional(rec, pattern) for pattern in patterns]
    shift_closed = [closed.subs({closed.ind_var: closed.ind_var - shift}) for closed, shift in zip(nonconditional, thresholds)]
    initials = [rec.initial] + [closed.eval_at(t) for closed, t in zip(shift_closed, thresholds[1:])]
    closed_forms = []
    for initial, closed, t in zip(initials, shift_closed, thresholds):
        mapping = {func(0): initial[func(t)] for func in rec.func_decls}
        closed_forms.append(closed.subs(mapping).subs(rec.initial))
    conditions = [sp.Interval(thresholds[i], thresholds[i + 1], left_open=False, right_open=True).as_relational(rec.ind_var) for i in range(len(thresholds) - 1)]
    return PiecewiseClosedForm(conditions, closed_forms, rec.ind_var)

def _compute_candidate_solution(rec: Recurrence, start, n, ith):
    values, index_seq = rec.get_n_values_starts_with(start, n)
    compressed_seq = utils.compress_seq(index_seq)
    guessed_patterns = [seq for seq, _ in compressed_seq]
    debug_prefix = "%dth guess starts with %dth value: " % (ith, start)
    padding = " "*len(debug_prefix)
    logger.debug(debug_prefix + "values are %s" % values)
    logger.debug(padding + "prefix of index sequence is %s" % index_seq)
    logger.debug(padding + "the guessed patterns are %s" % guessed_patterns)
    first_value = values[0]
    initial = {func.func(0): first_value[func] for func in first_value}
    new_rec = rec.copy_rec_with_diff_initial(initial)
    sol = _compute_solution_by_index_seq(new_rec, compressed_seq)
    # shift_sol = sol.subs({sol.ind_var: sol.ind_var - start})
    logger.debug(padding + "the guessed closed-form solution is %s" % sol)
    return sol, compressed_seq

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

def _set_up_constraints(rec: Recurrence, closed_form: PiecewiseClosedForm, index_seq):
    rec_conditions = [utils.to_z3(cond) for cond in rec.conditions]
    # intervals = closed_form.intervals
    k = z3.Int('k')
    constraint = True
    ind_var = utils.to_z3(closed_form.ind_var)
    for i, (seq, q) in enumerate(index_seq):
        # premise = utils.interval_to_z3(intervals[i], closed_form.ind_var)
        premise = utils.to_z3(closed_form.conditions[i])
        closed_form_component = closed_form.closed_forms[i]
        period = closed_form_component.period
        for r, j in enumerate(seq):
            closed_form_z3 = closed_form_component.to_z3()
            mapping = [(k, v) for k, v in closed_form_z3.items()]
            condition = z3.substitute(rec_conditions[j], *mapping)
            cur_constraint = z3.Implies(premise, condition)
            cur_constraint = z3.substitute(cur_constraint, (ind_var, period*k + r))
            constraint = z3.And(constraint, cur_constraint)
    return constraint, k
