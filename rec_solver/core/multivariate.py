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
    assert(len(array_func.nargs) == 1)
    nargs = list(array_func.nargs)[0]
    ts = [sp.Function('t%d' % i, nargs=1) for i in range(nargs - 1)] # the last argument is assumed to be the inductive variable
    all_array_apps = array_rec.get_all_array_app(array_func)
    transitions = []
    for app in all_array_apps:
        trans = {}
        for t, u, u_v in zip(ts, array_func.args, app.args):
            trans |= {t(d + 1): u_v.subs({u: t(d)}, simultaneous=True)}
        transitions.append(trans)
    for cond in array_rec.conditions:
        mapping = {u: t(d) for t, u in zip(ts, array_func.args)}
        print(cond.subs(mapping, simultaneous=True))
