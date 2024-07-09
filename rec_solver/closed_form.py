import z3
import sympy as sp
from . import utils

class PeriodicClosedForm:
    def __init__(self, closed_form_list, ind_var):
        self._closed_form_list = closed_form_list
        self._ind_var = ind_var

    def eval_at(self, n):
        if self.period == 1:
            r = 0
        else:
            assert(n >= 0)
            r = n % self.period
        val = {k.subs({self.ind_var: n}, simultaneous=True): c.subs({self.ind_var: n}, simultaneous=True) for k, c in self._closed_form_list[r].items()}
        return val

    def subs(self, mapping):
        new_list = []
        for part in self._closed_form_list:
            cur_closed = {k: c.subs(mapping, simultaneous=True) for k, c in part.items()}
            new_list.append(cur_closed)
        return PeriodicClosedForm(new_list, self.ind_var)

    def __str__(self):
        return str(self._closed_form_list)

    def get_rth_part_closed_form(self, r):
        return self._closed_form_list[r]

    def to_z3(self):
        ind_var_z3 = utils.to_z3(self.ind_var)
        closed_form_z3_list = [self._to_z3(closed) for closed in self._closed_form_list]
        res = {}
        for var in self.all_vars:
            var_z3 = utils.to_z3(var)
            expr_z3 = closed_form_z3_list[-1][var_z3]
            for i, closed in enumerate(closed_form_z3_list[:-1]):
                expr_z3 = z3.If(ind_var_z3 % self.period == i, closed[var_z3], expr_z3)
            res[var_z3] = z3.simplify(expr_z3)
        return res

    def _to_z3(self, closed):
        res = {}
        for k, c in closed.items():
            k_z3 = utils.to_z3(k)
            c_z3 = utils.to_z3(c)
            res[k_z3] = c_z3
        return res

    @property
    def period(self):
        return len(self._closed_form_list)

    @property
    def ind_var(self):
        return self._ind_var

    @property
    def all_vars(self):
        try:
            closed = self._closed_form_list[0]
            return set(closed.keys())
        except:
            return set()

class PiecewiseClosedForm:
    def __init__(self, conditions=[], closed_forms=[], ind_var=sp.Symbol('n', integer=True)):
        self._conditions = conditions
        self._closed_forms = closed_forms
        self._ind_var = ind_var

    def concatenate(self, latter_closed):
        conditions = self.conditions + latter_closed.conditions
        new_closed_forms = self.closed_forms + latter_closed.closed_forms
        return PiecewiseClosedForm(conditions, new_closed_forms, self.ind_var)

    def eval_at(self, n):
        assert(n >= 0)
        fired = [c.subs({self.ind_var: n}) for c in self.conditions]
        assert(any(fired))
        which = fired.index(True) - 1
        return self.closed_forms[which].subs({self.ind_var: n})

    def subs(self, mapping):
        conditions = [c.subs(mapping, simultaneous=True) for c in self.conditions]
        closed_forms = [c.subs(mapping) for c in self.closed_forms]
        return PiecewiseClosedForm(conditions, closed_forms, self.ind_var)

    def simple_subs(self, mapping):
        conditions = [c.subs(mapping, simultaneous=True) for c in self.conditions]
        closed_forms = [c.subs(mapping) for c in self.closed_forms]
        return PiecewiseClosedForm(conditions, closed_forms, self.ind_var)

    def to_z3(self):
        ind_var_z3 = utils.to_z3(self.ind_var)
        closed_forms_z3 = [closed.to_z3() for closed in self.closed_forms]
        res = {}
        for var in self.all_vars:
            var_z3 = utils.to_z3(var)
            expr_z3 = closed_forms_z3[0][var_z3]
            for i, interval in enumerate(self.intervals[:-1]):
                cond = utils.interval_to_z3(interval, self.ind_var)
                closed = closed_forms_z3[i][var_z3]
                expr_z3 = z3.If(cond, closed, expr_z3)
            res[var_z3] = z3.simplify(expr_z3)
        return res

    def __str__(self):
        res = ''
        max_prefix_len = max([len(str(cond)) for cond in self.conditions])
        for cond, closed in zip(self.conditions, self.closed_forms):
            res += '{0:{width}}: '.format(str(cond), width=max_prefix_len)
            res += str(closed) + '\n'
        return res

    def _compute_intervals(self, thresholds):
        res = []
        for i in range(len(thresholds) - 1):
            left = thresholds[i]
            right = thresholds[i + 1]
            res.append(sp.Interval(left, right, left_open=False, right_open=True))
        return res

    @property
    def closed_forms(self):
        return self._closed_forms

    @property
    def ind_var(self):
        return self._ind_var

    @property
    def conditions(self):
        return self._conditions

    @property
    def all_vars(self):
        try:
            return self.closed_forms[0].all_vars
        except:
            return set()

class SymbolicClosedForm:
    def __init__(self, constraints, closed_forms):
        self._constraints = constraints
        self._closed_forms = closed_forms

    def __str__(self):
        res = ''
        for constraint, closed in zip(self._constraints, self._closed_forms):
            res += str(constraint) + ':\n'
            res += '\t' + str(closed)
        return res

    def subs(self, mapping):
        constraints = [z3.substitute(c, *[(utils.to_z3(k), utils.to_z3(v)) for k, v in mapping.items()]) for c in self._constraints]
        closed_forms = [c.subs(mapping) for c in self._closed_forms]
        return SymbolicClosedForm(constraints, closed_forms)

    def to_z3(self):
        res = {}
        for var in self.all_vars:
            var_z3 = utils.to_z3(var)
            expr = self._closed_forms[-1].to_z3()[var_z3]
            for constraint, closed in zip(self._constraints[:-1], self._closed_forms[:-1]):
                expr = z3.If(constraint, closed.to_z3()[var_z3], expr)
            res[var_z3] = z3.simplify(expr)
        return res

    @property
    def all_vars(self):
        try:
            return self._closed_forms[0].all_vars
        except:
            return set()

class ExprClosedForm:
    def __init__(self, closed_forms, ind_var):
        self._closed_forms = closed_forms
        self._ind_var = ind_var

    def __str__(self):
        res = ''
        for expr, c in self._closed_forms.items():
            res += '%s: %s\n' % (expr, c)
        return res

    def subs(self, mapping):
        closed_forms = [c.subs(mapping) for c in self._closed_forms]
        return ExprClosedForm(closed_forms)

    def to_z3(self):
        res = {utils.to_z3(expr): utils.to_z3(c) for expr, c in self._closed_forms.items()}
        return res
