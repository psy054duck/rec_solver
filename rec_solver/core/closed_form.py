import z3
import sympy as sp
from . import utils
from collections import defaultdict

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

    def sympify(self):
        sympified = defaultdict(list)
        for i in range(self.period):
            cond = True
            if self.period != 1:
                cond = sp.Eq(self.ind_var % self.period, i)
            for f in self.closed_forms[i]:
                sympified[f].append((self.closed_forms[i][f], cond))
        return {f: sp.Piecewise(*sympified[f]) for f in sympified}

    def pprint(self):
        sp.init_printing()
        sp_dict = self.sympify()
        for f in sp_dict:
            sp.pprint(sp.Eq(f, sp_dict[f]))
            print()

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

    # def to_z3(self):
    #     ind_var_z3 = utils.to_z3(self.ind_var)
    #     closed_form_z3_list = [self._to_z3(closed) for closed in self._closed_form_list]
    #     res = {}
    #     for var in self.all_vars:
    #         var_z3 = utils.to_z3(var)
    #         expr_z3 = closed_form_z3_list[-1][var_z3]
    #         for i, closed in enumerate(closed_form_z3_list[:-1]):
    #             expr_z3 = z3.If(ind_var_z3 % self.period == i, closed[var_z3], expr_z3)
    #         res[var_z3] = z3.simplify(expr_z3)
    #     return res

    def to_z3(self):
        return self.selected_to_z3(self.all_vars)

    def selected_to_z3(self, vars):
        ind_var_z3 = utils.to_z3(self.ind_var)
        closed_form_z3_list = [self._to_z3(closed, vars) for closed in self._closed_form_list]
        res = {}
        for var in vars:
            var_z3 = utils.to_z3(var)
            expr_z3 = closed_form_z3_list[-1][var_z3]
            for i, closed in enumerate(closed_form_z3_list[:-1]):
                expr_z3 = z3.If(ind_var_z3 % self.period == i, closed[var_z3], expr_z3)
            res[var_z3] = z3.simplify(expr_z3)
        return res


    def _to_z3(self, closed, vars):
        res = {}
        for k in vars:
            c = closed[k]
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

    @property
    def conditions(self):
        return [i % self.period for i in range(self.period)]
    
    @property
    def closed_forms(self) -> list[dict]:
        return self._closed_form_list

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

    def sympify(self):
        expressions = defaultdict(list)
        for cond, closed in zip(self.conditions, self.closed_forms):
            sp_closed = closed.sympify()
            for f in sp_closed:
                expressions[f].append((sp_closed[f], cond))
        return {f: sp.Piecewise(*expressions[f]) for f in expressions}

    def pprint(self):
        sp.init_printing()
        sp_dict = self.sympify()
        for f in sp_dict:
            sp.pprint(sp.simplify(sp.Eq(f, sp_dict[f])))
            print()

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
            # for i, interval in enumerate(self.intervals[:-1]):
            for i, cond in enumerate(self.conditions):
                # cond = utils.interval_to_z3(interval, self.ind_var)
                closed = closed_forms_z3[i][var_z3]
                expr_z3 = z3.If(utils.to_z3(cond), closed, expr_z3)
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
    def closed_forms(self) -> list[PeriodicClosedForm]:
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
    def __init__(self, constraints, closed_forms, ind_var):
        self._constraints = constraints
        self._closed_forms = closed_forms
        self._ind_var = ind_var

    def __str__(self):
        res = ''
        for constraint, closed in zip(self._constraints, self._closed_forms):
            res += str(constraint) + ':\n'
            res += '\t' + str(closed)
        return res

    def sympify(self):
        expressions = defaultdict(list)
        for cond, closed in zip(self._constraints, self._closed_forms):
            sp_closed = closed.sympify()
            sp_cond = sp.parse_expr(str(cond))
            if sp_cond is True:
                sp_cond = sp.true
            to_integer_dict = {}
            for symbol in sp_cond.free_symbols:
                to_integer_dict[symbol] = sp.Symbol(symbol.name, integer=True)
            sp_cond = sp_cond.subs(to_integer_dict, simultaneous=True)
            for f in sp_closed:
                expressions[f].append((sp_closed[f].subs(to_integer_dict, simultaneous=True), sp_cond))
        for f in expressions:
            last_closed, _ = expressions[f][-1]
            expressions[f][-1] = (last_closed, True)
        # return {f: sp.piecewise_exclusive(sp.piecewise_fold(sp.Piecewise(*expressions[f]))) for f in expressions}
        return {f: sp.piecewise_fold(sp.Piecewise(*expressions[f])) for f in expressions}

    def pprint(self):
        sp.init_printing()
        sp_dict = self.sympify()
        for f in sp_dict:
            sp.pprint(sp.simplify(sp.Eq(f, sp_dict[f])))
            print()

    def subs(self, mapping):
        constraints = [z3.substitute(c, *[(utils.to_z3(k), utils.to_z3(v)) for k, v in mapping.items()]) for c in self._constraints]
        closed_forms = [c.subs(mapping) for c in self._closed_forms]
        return SymbolicClosedForm(constraints, closed_forms, self.ind_var)

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
    def ind_var(self):
        return self._ind_var

    @property
    def conditions(self):
        conditions = []
        for cons, piece_closed in zip(self._constraints, self.closed_forms):
            for piece_cond, periodic_closed in zip(piece_closed.conditions, piece_closed.closed_forms):
                period = periodic_closed.period
                for i in range(period):
                    cond = sp.sympify(str(cons)) & piece_cond & (self.ind_var % period == i)
                    conditions.append(sp.simplify(cond))
        return conditions

    @property
    def transitions(self):
        closed_forms = []
        for piece_closed in self.closed_forms:
            for periodic_closed in piece_closed.closed_forms:
                closed_forms.extend(periodic_closed.closed_forms)
        return closed_forms
                
    @property
    def closed_forms(self) -> list[PiecewiseClosedForm]:
        return self._closed_forms

    @property
    def cases(self):
        return self._constraints

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

    def is_trivial(self):
        if len(self._closed_forms) == 1:
            v = list(self._closed_forms.keys())[0]
            if v == 1:
                return True
        return False

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

    def as_dict(self):
        return self._closed_forms.copy()

class MultiFuncClosedForm:
    def __init__(self, func_decl, closed_form):
        self._func_decl = func_decl
        self._closed_form = sp.simplify(closed_form)

    @property
    def func_decl(self):
        return self._func_decl

    def sympify(self):
        return {self.func_decl: self.closed_form}

    @property
    def closed_form(self):
        return self._closed_form.copy()

    def to_z3(self):
        return {utils.to_z3(self.func_decl): utils.to_z3(self._closed_form)}

    def __str__(self):
        return "%s: %s" % (self.func_decl, self.closed_form)
