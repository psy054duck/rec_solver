import sympy as sp
import z3
from ..recurrence import MultiRecurrence, Recurrence, LoopRecurrence
from .ultimately_periodic import solve_ultimately_periodic_symbolic
from .. import utils
from functools import reduce

def multirec2loop(rec: MultiRecurrence):
    pass

def solve_nearly_tail(rec: MultiRecurrence):
    assert(rec.is_nearly_tail())
    d = sp.Symbol('_d', integer=True)
    D = sp.Symbol('_D', integer=True)
    ret = sp.Symbol('_ret', integer=True)
    loop_rec = nearly_tail2loop(rec, d, ret)
    loop_guard = get_loop_cond(rec, d)
    loop_closed_form = solve_ultimately_periodic_symbolic(loop_rec)
    loop_closed_form.pprint()
    piecewise_D = compute_piecewise_D(d, D, loop_guard, loop_closed_form)
    scalar_closed_form = loop_closed_form.subs({d: piecewise_D})
    base_conditions, base_post_ops = rec.get_base_cases()
    branches = []
    for cond, op in zip(base_conditions, base_post_ops):
        args = cond.free_symbols | op.free_symbols
        symbol2func_mapping = {arg: symbol2func(arg)(d) for arg in args}
        op_func = op.subs(symbol2func_mapping, simultenoues=True)
        cond_func = cond.subs(symbol2func_mapping, simultaneous=True)
        op_D = op_func.subs(scalar_closed_form.sympify(), simultaneous=True)
        cond_D = cond_func.subs(scalar_closed_form.sympify(), simultaneous=True)
        branches.append((op_D, cond_D))
    branches[-1] = (branches[-1][0], True)
    ret0 = sp.piecewise_fold(sp.Piecewise(*branches))
    closed_form_dict = scalar_closed_form.sympify()
    return sp.piecewise_fold(closed_form_dict[symbol2func(ret)(d)].subs({ret: ret0}))

def nearly_tail2loop(rec: MultiRecurrence, d, ret):
    assert(rec.is_nearly_tail())
    # recursive_calls = rec.recursive_calls
    # post_ops = rec.post_ops
    func_sig = rec.func_sig
    args = func_sig.args
    # d = sp.Symbol('_d', integer=True)
    # ret = sp.Symbol('_ret', integer=True)
    args_func_map = {arg: symbol2func(arg) for arg in args} | {ret: symbol2func(ret)}
    # base_conditions, base_post_ops = rec.get_base_cases()
    rec_conditions, recursive_calls, rec_post_ops = rec.get_rec_cases()
    args_func_d = {arg: symbol2func(arg)(d) for arg in args}
    args_func_d_1 = {arg: symbol2func(arg)(d + 1) for arg in args}
    loop_branch_conditions = [cond.subs(args_func_d, simultaneous=True) for cond in rec_conditions]
    transitions = []
    for i, rec_call in enumerate(recursive_calls):
        args_p = list(rec_call.values())[0].args
        post_op = rec_post_ops[i]
        transition = {args_func_d_1[arg]: arg_p.subs(args_func_d, simultaneous=True) for arg, arg_p in zip(args, args_p)}
        name_rec = list(rec_call.keys())[0]
        ret_func = symbol2func(ret)
        transition |= {ret_func(d + 1): post_op.subs({name_rec: ret_func(d)} | args_func_d, simultaneous=True)}
        transitions.append(transition)
    initial = {args_func_map[ret](0): ret} | {symbol2func(arg)(0): arg for arg in args}
    loop_rec = LoopRecurrence.mk_rec(initial, loop_branch_conditions, transitions)
    return loop_rec

def get_loop_cond(rec: MultiRecurrence, d):
    assert(rec.is_nearly_tail())
    base_conditions, _ = rec.get_base_cases()
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
    closed_form = solve_nearly_tail(rec)
    # sp.pprint(sp.simplify(closed_form))
    return sp.simplify(closed_form)
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
