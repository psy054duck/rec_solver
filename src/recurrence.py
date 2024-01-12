import sympy as sp
from . import utils
from functools import reduce

class Recurrence:
    def __init__(self, initial, branches):
        self._preprocess(initial, branches)

    def _preprocess(self, initial, branches):
        self._conditions = [branch[0] for branch in branches]
        self._transitions = [branch[1] for branch in branches]
        self._initial = initial
        app = self.get_app()
        last_args = {a.args[-1] for a in app}
        if len(last_args) != 1:
            raise Exception("More than one induction variable")
        self._ind_var = last_args.pop()

    def get_first_n_values(self, n):
        assert(self.is_standard())

    def is_solvable_map(self):
        '''By solvable map, we mean all x(n) can be divided into x_1(n) v x_2(n) ... v x_m(n), such that x_i(n+1) = Kx_i(n) + p(x_1(n), ..., x_{i-1}(n)) + ep(n)'''
        assert(self.is_standard())
        if not self.conditions[0]: return False
        ind_var = self.get_ind_var()
        functions = self.get_all_func()
        if any((func.nargs > 1 for func in functions)): return False
        func_apps = [func(ind_var) for func in functions]


    @property
    def ind_var(self):
        return self._ind_var

    @property
    def conditions(self):
        return self._conditions.copy()

    @property
    def transitions(self):
        return self._transitions.copy()

    @property
    def initial(self):
        return self._initial.copy()

    def get_app(self):
        terms = self._get_app_from_conditions() | self._get_app_from_transitions()
        return terms

    def is_linear(self):
        app = self.get_app()
        for trans in self.transitions:
            if not all(utils.is_linear(expr, app) for expr in trans.values()):
                return False
        return True

    def is_linear_conditional(self):
        terms = self.get_terms()

    def get_all_func(self):
        app_condition = self._get_app_from_conditions()
        app_trans = self._get_app_from_transitions()
        functions_initial = self._get_initial_func()
        functions_cond_trans = {app.func for app in app_condition | app_trans if not app.is_Symbol}
        return functions_initial | functions_cond_trans

    def is_standard(self):
        '''Check whether this recurrence is in the standard form.
           By standard form, we mean in the transitions, left-hand sides are all of form f(..., n+1) and right-hand sides are all of form f(..., n).'''
        ind_var = self.ind_var
        for trans in self.transitions:
            for lhs, rhs in trans.items():
                if lhs.is_number or not lhs.func.is_Function or not sp.Eq(lhs.args[-1] - ind_var - 1, 0):
                    return False
                rhs_app = {app for app in utils.get_app(rhs) if not app.is_Symbol}
                for app in rhs_app:
                    if app.is_number or not app.func.is_Function or not sp.Eq(app.args[-1] - ind_var, 0):
                        return False
        return True

    def _get_app_from_conditions(self):
        app = reduce(set.union, [utils.get_app(cond) for cond in self.get_conditions()])
        return app

    def _get_app_from_transitions(self):
        app = set()
        for trans in self.transitions():
            trans_app = reduce(set.union, [utils.get_app(expr) for expr in trans.values()])
            app |= trans_app
        return app

    def _get_initial_func(self):
        return {app.func for app in self.initial if not app.is_Symbol}
