import sympy as sp
from ..recurrence import Recurrence
from .ultimately_periodic import solve_ultimately_periodic_symbolic

def solve_multivariate_rec(rec: Recurrence):
    scalar_rec = rec.project_to_scalars()
    array_rec = rec.project_to_arrays()
    scalar_closed = solve_ultimately_periodic_symbolic(scalar_rec)
    d = sp.Symbol('d', integer=True)
    scalar_closed_d = scalar_closed.subs({rec.ind_var: rec.ind_var - d - 1})
    assert(len(array_rec.all_array_func) == 1)
    array_func = array_rec.all_array_func[0]
    array_func_next = array_func.subs({rec.ind_var: rec.ind_var + 1})
    assert(len(array_func.nargs) == 1)
    nargs = list(array_func.nargs)[0]
    ts = [sp.Function('t%d' % i, nargs=1) for i in range(nargs - 1)] # the last argument is assumed to be the inductive variable
    all_array_apps = array_rec.get_all_array_app(array_func)
    t_transitions = []
    coeffs = []
    transitions_scalar_part = []
    for app, trans in zip(all_array_apps, array_rec.transitions):
        t_trans = {}
        cur_trans = trans[array_func_next]
        c = cur_trans.coeff(app)
        coeffs.append(c)
        transitions_scalar_part.append(cur_trans - c*app)
        for t, u, u_v in zip(ts, array_func.args, app.args):
            t_trans |= {t(d + 1): u_v.subs({u: t(d)}, simultaneous=True)}
        t_transitions.append(t_trans)

    branches = []
    e = sp.Function('e', nargs=1)
    acc = sp.Function('acc', nargs=1)
    for ori_cond, t_trans, c, scalar_part in zip(array_rec.conditions, t_transitions, coeffs, transitions_scalar_part):
        u_map_t = {u: t(d) for t, u in zip(ts, array_func.args)}
        for closed_cond, closed in zip(scalar_closed_d.conditions, scalar_closed_d.transitions):
            ori_cond_u_t = ori_cond.subs(u_map_t, simultaneous=True)
            ori_cond_subs = ori_cond_u_t.subs(closed, simultaneous=True)
            closed_cond_subs = closed_cond.subs(closed, simultaneous=True)
            scalar_part_subs = scalar_part.subs(closed, simultaneous=True)
            cond = ori_cond_subs & closed_cond_subs
            trans = t_trans | {e(d + 1): c*e(d)} | {acc(d+1): acc(d) + scalar_part_subs*e(d)}
            branches.append((cond, trans))
            # mapping |= {}
    zero = sp.Integer(0)
    initial = {t(zero): arg for t, arg in zip(ts, array_func.args)} | {e(zero): sp.Integer(1)} | {acc(zero): zero}
    t_rec = Recurrence(initial, branches)
    t_closed = solve_ultimately_periodic_symbolic(t_rec)
    print('*'*100)
    print(t_closed.subs({d: rec.ind_var}))
        # print(cond.subs(mapping, simultaneous=True))
