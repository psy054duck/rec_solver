import logging
import sympy as sp
import z3
from ..recurrence import MultiRecurrence, Recurrence, LoopRecurrence
from .ultimately_periodic import solve_ultimately_periodic_symbolic
from .. import utils
from functools import reduce
from collections import defaultdict
from itertools import product

class PivotCall:
    '''This class represents a pivot call for a recursive case where there are
    multiple recursive calls. Pivot call is one of those recursive calls s.t.
    all other calls have been computed during the computation of pivot call.'''
    def __init__(self):
        pass

logger = logging.getLogger(__name__)
def rec2nearly_tail(rec: MultiRecurrence):
    assert(rec.number_ret() == 1)
    pivot_calls = get_pivot_calls(rec)
    # new_func = sp.Function('')
    func_sig = rec.func_sig
    func_p = sp.Function(func_sig.name + '_p')
    print(pivot_calls)

def refine_cached_computation_one_rec_case(pivot_call, rec_cond, rec_call, post_ops, rec: MultiRecurrence):
    pivot_f, cached_computation = pivot_call
    base_conditions, _ = rec.get_base_cases()
    rec_conditions, _, _ = rec.get_rec_cases()
    base_new_condition = rec_cond & reduce(sp.Or, base_conditions)


def get_pivot_calls(rec: MultiRecurrence):
    '''Pivot calls are those calls in recursive cases whose computations also
    compute other recursive calls in the same case. This function returns the
    list of tuple of form (pivot_call, cached_computation) in the same order of
    recursive cases stored in rec'''
    # rec_conditions, rec_calls, rec_ops = rec.get_rec_cases()
    rec_cases = rec.get_rec_cases()
    all_pivot_calls = []
    # for pre_cond, calls in zip(rec_conditions, rec_calls):
    for rec_case in rec_cases:
        pre_cond = rec_case.condition
        calls = rec_case.recursive_calls
        if len(calls) <= 1:
            continue
        name_terms = {}
        for name, call in calls.items():
            equal_terms = eq_terms(call, pre_cond, rec)
            name_terms[name] = equal_terms
            name_terms[name].add(call)
        for pivot_call_name, pivot_call in calls.items():
            other_names = set(name_terms.keys()) - {pivot_call_name}
            is_all_computed = True
            cached_dict = {}
            for other_name in other_names:
                redundant_computation = [is_computed(pivot_call, other_call, pre_cond, rec) for other_call in name_terms[other_name]]
                cached_computations = [r for r in redundant_computation if len(r[0]) != 0 or len(r[1]) != 0]
                # is_all_redundant = any([(len(r[0]) != 0 or len(r[1]) != 0) for r in redundant_computation])
                # if all([not is_computed(pivot_call, other_call, pre_cond, rec) for other_call in name_terms[other_name]]):
                if len(cached_computations) == 0:
                    is_all_computed = False
                    break
                cached_computation = cached_computations[0]
                cached_dict[other_name] = cached_computation
            if is_all_computed:
                all_pivot_calls.append((pivot_call_name, cached_dict))
                break
        else:
            raise Exception('Not convertible')
    return all_pivot_calls


def is_computed(pivot_call, other_call, pre_cond, rec):
    '''Check if in the computation of target_call, other_call is also computed'''
    unrolled_pivot_call = unroll(pivot_call, rec)
    unrolled_other_call = unroll(other_call, rec)
    base_pivot_conditions = [case.condition for case in unrolled_pivot_call.get_base_cases()]
    # base_other_conditions, base_other_post_ops = unrolled_other_call.get_base_cases()
    base_other_conditions = [case.condition for case in unrolled_other_call.get_base_cases()]
    base_other_post_ops = [case.op for case in unrolled_other_call.get_base_cases()]
    total_other_base_cond = reduce(sp.Or, base_other_conditions, sp.false)
    solver = z3.Solver()
    # if the pivot call goes into a base case, then other call should also goes into a base case
    if any([solver.check(utils.to_z3(pre_cond & base_target_cond & sp.Not(total_other_base_cond))) == z3.sat for base_target_cond in base_pivot_conditions]):
        return [], []
    base_res = []
    # for base_pivot_cond in base_pivot_conditions:
    for pivot_base_case in unrolled_pivot_call.get_base_cases():
        computed = [z3.unsat == solver.check(utils.to_z3(pre_cond & pivot_base_case.condition & sp.Not(base_other_cond))) for base_other_cond in base_other_conditions]
        cur_op = [(base_other_post_ops[i], base_other_conditions[i]) for i, c in enumerate(computed) if c]
        cur_op[-1] = (cur_op[-1][0], sp.true)
        base_res.append(sp.Piecewise(*cur_op))
    # rec_pivot_conditions, rec_pivot_calls_list, _ = unrolled_pivot_call.get_rec_cases()
    rec_res = []
    # for rec_pivot_cond, rec_pivot_calls in zip(rec_pivot_conditions, rec_pivot_calls_list):
    for rec_case in unrolled_pivot_call.get_rec_cases():
        # if the pivot call goes into a recursive case (i), then
        # (1) if other call goes into a base case, it is okay;
        # (2) if other call goes in to a recursive case, then it should be equal
        # to some call in the recursive case (i)
        rec_pivot_cond = rec_case.condition
        rec_pivot_calls = rec_case.recursive_calls
        name_list = list(rec_pivot_calls.keys())
        if z3.unsat == solver.check(utils.to_z3(pre_cond & rec_pivot_cond)):
            rec_res.append({})
            continue
        computed = [z3.unsat == solver.check(utils.to_z3(pre_cond & rec_pivot_cond & sp.Not(rec_pivot_calls[name] == other_call))) for name in name_list]
        if not any(computed):
            return [], []
        try:
            idx = computed.index(True)
            cur_res = {name_list[idx]}
            rec_res.append(cur_res)
        except ValueError:
            return [], []

        # if all(computed):
        #     return False
        
        # if all([z3.sat == solver.check(utils.to_z3(pre_cond & rec_pivot_cond & sp.Not(rec_pivot_calls[name] == other_call))) for name in rec_pivot_calls]):
        #     return False
    return base_res, rec_res

def unroll(call, rec) -> MultiRecurrence:
    '''unroll the call according to the rec definition'''
    func_sig = rec.func_sig
    arity = len(func_sig.args)
    unroll_mapping = {func_sig.args[i]: call.args[i] for i in range(arity)}
    unrolled_rec = rec.subs(unroll_mapping)
    return unrolled_rec

def eq_terms(target_call, pre_cond, rec: MultiRecurrence):
    unrolled_rec = unroll(target_call, rec)
    # base_conditions, base_post_ops = unrolled_rec.get_base_cases()
    base_cases = unrolled_rec.get_base_cases()
    # rec_conditions, recursive_calls, rec_post_ops = unrolled_rec.get_rec_cases()
    rec_cases = unrolled_rec.get_rec_cases()
    solver = z3.Solver()
    # for cond, ops in zip(base_conditions, base_post_ops):
    base_conditions = [case.condition for case in base_cases]
    for base_case in base_cases:
        cond = base_case.condition
        ops = base_case.op
        path_cond = pre_cond & sp.Not(reduce(sp.Or, base_conditions, sp.false)) & sp.Not(cond)
        path_cond_z3 = utils.to_z3(path_cond)
        res = solver.check(path_cond_z3)
        if res == z3.unsat:
            return {ops}
    # for cond, calls, ops in zip(rec_conditions, recursive_calls, rec_post_ops):
    for rec_case in rec_cases:
        cond = rec_case.condition
        calls = rec_case.recursive_calls
        ops = rec_case.op
        path_cond = pre_cond & sp.Not(reduce(sp.Or, base_conditions, sp.false)) & sp.Not(cond)
        path_cond_z3 = utils.to_z3(path_cond)
        res = solver.check(path_cond_z3)
        if res == z3.unsat:
            return {op.subs(calls, simultaneous=True) for op in ops} if set(ops) == set(calls.keys()) else set()


def solve_nearly_tail(rec: MultiRecurrence):
    assert(rec.is_nearly_tail())
    d = sp.Symbol('_d', integer=True)
    D = sp.Symbol('_D', integer=True)
    # ret = sp.Symbol('_ret', integer=True)
    rets = sp.symbols('_ret:%d' % rec.number_ret())
    loop_rec = nearly_tail2loop(rec, d, rets)
    loop_guard = get_loop_cond(rec, d)
    loop_closed_form = solve_ultimately_periodic_symbolic(loop_rec)
    # loop_closed_form.pprint()
    piecewise_D = compute_piecewise_D(d, D, loop_guard, loop_closed_form)
    scalar_closed_form = loop_closed_form.subs({d: piecewise_D})
    # base_conditions, base_post_ops = rec.get_base_cases()
    branches_rets = [[] for _ in range(len(rets))]
    # for cond, ops in zip(base_conditions, base_post_ops):
    for base_case in rec.get_base_cases():
        cond = base_case.condition
        ops = base_case.op
        args = cond.free_symbols | reduce(set.union, [op.free_symbols for op in ops])
        symbol2func_mapping = {arg: symbol2func(arg)(d) for arg in args}
        op_funcs = (op.subs(symbol2func_mapping, simultenoues=True) for op in ops)
        cond_func = cond.subs(symbol2func_mapping, simultaneous=True)
        ops_D = (op_func.subs(scalar_closed_form.sympify(), simultaneous=True) for op_func in op_funcs)
        cond_D = cond_func.subs(scalar_closed_form.sympify(), simultaneous=True)
        for branches, op_D in zip(branches_rets, ops_D):
            branches.append((op_D, cond_D))
    for branches in branches_rets:
        branches[-1] = (branches[-1][0], True)
    # ret0 = sp.piecewise_fold(sp.Piecewise(*branches))
    rets0 = [sp.piecewise_fold(sp.Piecewise(*branches)) for branches in branches_rets]
    closed_form_dict = scalar_closed_form.sympify()
    return [sp.piecewise_fold(closed_form_dict[symbol2func(ret)(d)].subs({ret: ret0})) for ret, ret0 in zip(rets, rets0)]

def nearly_tail2loop(rec: MultiRecurrence, d, rets):
    assert(rec.is_nearly_tail())
    # recursive_calls = rec.recursive_calls
    # post_ops = rec.post_ops
    func_sig = rec.func_sig
    args = func_sig.args
    # d = sp.Symbol('_d', integer=True)
    # ret = sp.Symbol('_ret', integer=True)
    args_func_map = {arg: symbol2func(arg) for arg in args} | {ret: symbol2func(ret) for ret in rets}
    # base_conditions, base_post_ops = rec.get_base_cases()
    # rec_conditions, recursive_calls, rec_post_ops = rec.get_rec_cases()
    args_func_d = {arg: symbol2func(arg)(d) for arg in args}
    args_func_d_1 = {arg: symbol2func(arg)(d + 1) for arg in args}
    rec_conditions = [case.condition for case in rec.get_rec_cases()]
    loop_branch_conditions = [cond.subs(args_func_d, simultaneous=True) for cond in rec_conditions]
    transitions = []
    # for i, rec_call in enumerate(recursive_calls):
    for rec_case in rec.get_rec_cases():
        rec_call = rec_case.recursive_calls
        args_p = list(rec_call.values())[0].args
        # post_ops = rec_post_ops[i]
        post_ops = rec_case.op
        transition = {args_func_d_1[arg]: arg_p.subs(args_func_d, simultaneous=True) for arg, arg_p in zip(args, args_p)}
        name_rec = list(rec_call.keys())[0]
        ret_funcs = [symbol2func(ret) for ret in rets]
        transition |= {ret_func(d + 1): post_op.subs({name_rec: ret_func(d)} | args_func_d, simultaneous=True) for ret_func, post_op in zip(ret_funcs, post_ops)}
        transitions.append(transition)
    initial = {args_func_map[ret](0): ret for ret in rets} | {symbol2func(arg)(0): arg for arg in args}
    loop_rec = LoopRecurrence.mk_rec(initial, loop_branch_conditions, transitions)
    return loop_rec

def get_loop_cond(rec: MultiRecurrence, d):
    assert(rec.is_nearly_tail())
    # base_conditions, _ = rec.get_base_cases()
    base_conditions = [case.condition for case in rec.get_base_cases()]
    func_sig = rec.func_sig
    args = func_sig.args
    args_func_d = {arg: symbol2func(arg)(d) for arg in args}
    disjunct_base_condition = reduce(sp.Or, base_conditions, sp.false)
    functional_base_condition = disjunct_base_condition.subs(args_func_d, simultaneous=True)
    return functional_base_condition

def compute_piecewise_D(d, D, loop_cond, loop_closed_form):
    '''Assume D is piecewise linear'''
    d_z3 = utils.to_z3(d)
    D_z3 = utils.to_z3(D)
    branches = []
    for case, closed in zip(loop_closed_form.cases, loop_closed_form.closed_forms):
        terminate_cond = loop_cond.subs(closed.sympify(), simultaneous=True)
        terminate_cond = sp.piecewise_exclusive(sp.piecewise_fold(terminate_cond), skip_nan=True)
        sp_case = utils.to_sympy(case)
        cur_D = compute_D_by_case(d_z3, D_z3, sp.Not(terminate_cond), sp_case)
        branches.append((cur_D, sp_case))
    branches[-1] = (branches[-1][0], True)
    return sp.simplify(sp.Piecewise(*branches))


def compute_D_by_case(d, D, loop_cond, case):
    '''Assume D is linear under the case'''
    cond = utils.to_z3(loop_cond)
    case_z3 = utils.to_z3(case)
    axioms = set()
    # smallest D that violates the loop condition
    axioms.add(case_z3)
    axioms.add(z3.ForAll([d], z3.Implies(z3.And(0 <= d, d < D), cond)))
    axioms.add(z3.substitute(z3.Not(cond), (d, D)))
    axioms.add(D >= 0)

    # first apply QE and assume that the result is linear
    tactic = z3.Tactic('qe')
    constraints = z3.And(*tactic(z3.And(*axioms))[0])
    args = [utils.to_z3(s) for s in loop_cond.free_symbols | case.free_symbols]
    coeffs = [z3.Int('_c%d' % i) for i in range(len(args))]
    affine_term = z3.Int('_c%d' % len(args))
    linear_comb = sum([c*a for c, a in zip(coeffs, args)]) + affine_term
    deno = z3.Int('_deno')
    solver = z3.Solver()
    # solver.add(case)
    solver.add(z3.ForAll(args + [D], z3.Implies(constraints, deno*D == linear_comb)))
    solver.add(deno != 0)
    # print(solver)
    bnd = 5
    #TODO if constraints are assumed to be linear,
    #     then this query should also be linear by farkas lemma
    for _ in range(bnd):
        res = solver.check()
        if res == z3.sat or res == z3.unsat:
            break
    if res == z3.sat:
        m = solver.model()
    else:
        raise Exception('cannot compute D')
    return utils.to_sympy(m.eval(linear_comb/deno))

def symbol2func(sym):
    return sp.Function(sym.name, nargs=1)

def solve_multivariate_rec(rec: MultiRecurrence):
    if rec.is_nearly_tail():
        closed_forms = solve_nearly_tail(rec)
    else:
        rec2nearly_tail(rec)
        # raise Exception('not a nearly tail recursion')
    # sp.pprint(sp.simplify(closed_form))
    return [sp.simplify(closed_form) for closed_form in closed_forms]
# f(n, M)
#   if base_1(n): Mb_1
#   elif base_2(n): Mb_2
#   else: f(vn, M1M)

# f(n)
#   ret(0) = if base(n(D)) b else ....
#   n(0) = n
#   M = I
#   while (!base_1(n(d)) && !base_2(n(d)))
#       if (phi(n(d))):
#           n(d + 1) = vn(d)
#           M(d + 1) = M1M(d)
#           
