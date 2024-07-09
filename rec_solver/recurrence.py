import sympy as sp
from sympy.core.function import AppliedUndef
from . import utils
from functools import reduce

class Recurrence:
    def __init__(self, initial, branches):
        self._preprocess(initial, branches)
        self.cached_result = {}

    def _preprocess(self, initial, branches):
        conditions = [branch[0] for branch in branches]
        self._conditions = Recurrence.make_exclusive_conditions(conditions)
        self._transitions = [branch[1] for branch in branches]
        self._initial = initial
        app = self.get_app()
        last_args = {a.args[-1] for a in app if not a.is_Symbol}
        if len(last_args) != 1:
            raise Exception("More than one induction variable")
        self._ind_var = last_args.pop()
        self._transitions = self._padding_transitions(self._transitions, self.all_funcs)
        self._func_decls = self._get_all_func_decl()
        zero_indexed_func_apps = [func_decl(sp.Integer(0)) for func_decl in self.func_decls if all([narg == 1 for narg in func_decl.nargs])]
        self._initial = {zero_app: initial.get(zero_app, zero_app) for zero_app in zero_indexed_func_apps}
        self._closed_forms = {}

    def _padding_transitions(self, transitions, all_funcs):
        new_transitions = []
        all_funcs_next = [func.subs({self.ind_var: self.ind_var + 1}) for func in all_funcs]
        for trans in transitions:
            need_padding = set(all_funcs_next) - set(trans.keys())
            identity_trans = {k: k.subs({self.ind_var: self.ind_var - 1}) for k in need_padding}
            new_transitions.append(trans | identity_trans)
        return new_transitions

    def simplify_with_partial_solution(self, closed_forms):
        self._conditions = [branch.subs(closed_forms) for branch in self._conditions]
        self._transitions = [{k: v.subs(closed_forms) for k, v in trans.items()} for trans in self._transitions]
        self._closed_forms |= closed_forms

    def subs(self, mapping):
        initial = {k: self.initial[k].subs(mapping, simultaneous=True) for k in self.initial}
        conditions = [c.subs(mapping, simultaneous=True) for c in self.conditions]
        transitions = [{k: trans[k].subs(mapping, simultaneous=True) for k in trans} for trans in self.transitions]
        branches = list(zip(conditions, transitions))
        return Recurrence(initial, branches)

    def copy_rec_with_diff_initial(self, new_initial):
        branches = list(zip(self.conditions, self.transitions))
        return Recurrence(new_initial, branches)

    @staticmethod
    def make_exclusive_conditions(conditions):
        acc_neg = sp.true
        exclusive_conditions = []
        for cond in conditions:
            exclusive_conditions.append(sp.simplify(sp.And(acc_neg, cond)))
            acc_neg = sp.And(acc_neg, sp.Not(cond))
        return exclusive_conditions

    def get_n_values_starts_with(self, start, n):
        first_values, index_seq = self.get_first_n_values(start + n)
        return first_values[start:], index_seq[start:]

    def get_first_n_values(self, n):
        assert(self.is_standard())
        first_n_values = [self.initial]
        conditions = self.conditions
        transitions = self.transitions
        index_seq = []
        for i in range(n):
            cur_values = first_n_values[-1]
            # cur_transitions = [{k.subs(self.ind_var, i): trans[k].subs(self.ind_var, i) for k in trans} for trans in transitions]
            cur_conditions = [cond.subs(self.ind_var, i) for cond in conditions]
            for cond_index, cond in enumerate(cur_conditions):
                if cond.subs(cur_values).simplify() == sp.true:
                    cur_transition = {k.subs(self.ind_var, i): v.subs(self.ind_var, i) for k, v in transitions[cond_index].items()}
                    true_values = {k: v.subs(cur_values) for k, v in cur_transition.items()}
                    first_n_values.append(true_values)
                    index_seq.append(cond_index)
                    break
        return first_n_values, index_seq

    def is_all_initialized(self):
        return all((func_decl(0) in self.initial for func_decl in self.func_decls))

    def run_one_iteration_for_ith_transition(self, cur_value, ith):
        transition = self.transitions[ith]
        val = {v: transition[v].subs(cur_value, simultaneous=True) for v in transition}
        val = {k.func(self.ind_var): val[k] for k in val}
        return val

    def project_to_scalars(self):
        initial = self.initial
        scalar_funcs = [func.subs({self.ind_var: self.ind_var + 1}, simultaneous=True) for func in self.all_scalar_func]
        transitions = [{k: v for k, v in trans.items() if k in scalar_funcs} for trans in self.transitions]
        # branches = list(zip(self.conditions, transitions))
        removed = []
        conditions = []
        for i in range(len(transitions)):
            if i in removed: continue
            cond = self.conditions[i]
            for j in range(i + 1, len(transitions)):
                if j in removed: continue
                if utils.is_same_transition(transitions[i], transitions[j]):
                    removed.append(j)
                    cond = sp.Or(cond, self.conditions[j])
            conditions.append(sp.simplify(cond))
        filtered_transitions = [transitions[i] for i in range(len(transitions)) if i not in removed]
        assert(len(conditions) == len(filtered_transitions))
        branches = list(zip(conditions, filtered_transitions))
        return Recurrence(initial, branches)

    def project_to_arrays(self):
        initial = {}
        array_funcs = [func.subs({self.ind_var: self.ind_var + 1}, simultaneous=True) for func in self.all_array_func]
        transitions = [{k: v for k, v in trans.items() if k in array_funcs} for trans in self.transitions]
        branches = list(zip(self.conditions, transitions))
        return Recurrence(initial, branches)

    @property
    def closed_forms(self):
        return self._closed_forms.copy()

    @property
    def func_decls(self):
        return self._func_decls.copy()

    @property
    def all_funcs(self):
        funcs = reduce(set.union, [set(trans.keys()) for trans in self.transitions])
        return [func.subs({self.ind_var: self.ind_var - 1}) for func in funcs]

    @property
    def ind_var(self):
        return self._ind_var

    @ind_var.setter
    def ind_var(self, var):
        self._ind_var = var

    @property
    def conditions(self):
        return self._conditions.copy()

    @property
    def transitions(self):
        return self._transitions.copy()

    @property
    def initial(self):
        return self._initial.copy()

    @property
    def all_scalar_func(self):
        return [func for func in self.all_funcs if all([narg == 1 for narg in func.nargs])]

    @property
    def all_array_func(self):
        return [func for func in self.all_funcs if all([narg != 1 for narg in func.nargs])]

    def get_all_array_app(self, array_func):
        k = array_func.subs({self.ind_var: self.ind_var + 1}, simultaneous=True)
        res = []
        for trans in self.transitions:
            app = [i for i in trans[k].atoms(sp.Function) if isinstance(i, AppliedUndef) and i.func == array_func.func]
            assert(len(app) <= 1)
            if len(app) == 0:
                app = array_func
            else:
                app = app[0]
            res.append(app)
        return res

    @classmethod
    def build_nonconditional_from_rec_by_seq(cls, rec, seq, initial):
        transitions = rec.transitions
        ind_var = rec.ind_var
        func_decls = rec.func_decls
        transition = {func_decl(ind_var + 1): func_decl(ind_var) for func_decl in func_decls}
        for i in seq:
            cur_transition = transitions[i]
            new_cur_transition = {func_app.func(ind_var): trans for func_app, trans in cur_transition.items()}
            transition = {func_app: trans.subs(new_cur_transition, simultaneous=True) for func_app, trans in transition.items()}
        return cls(initial, [(sp.true, transition)])

    def get_app(self):
        terms = self._get_app_from_conditions() | self._get_app_from_transitions()
        return terms

    def is_linear(self):
        app = self.get_app()
        for trans in self.transitions:
            if not all(utils.is_linear(expr, app) for expr in trans.values()):
                return False
        return True

    def get_symbolic_values(self):
        initial = self.initial
        from_initial = reduce(set.union, [v.free_symbols for v in initial.values()], set())
        from_condition = reduce(set.union, [cond.free_symbols for cond in self.conditions], set())
        _from_transition = reduce(set.union, [trans.values() for trans in self.transitions], set())
        from_transition = reduce(set.union, [trans.free_symbols for trans in _from_transition], set())
        return (from_initial | from_condition | from_transition) - {self.ind_var}

    def is_linear_conditional(self):
        terms = self.get_terms()

    def _get_all_func_decl(self):
        app_condition = self._get_app_from_conditions()
        app_trans = self._get_app_from_transitions()
        functions_initial = self._get_initial_func()
        functions_cond_trans = {app.func for app in app_condition | app_trans if not app.is_Symbol}
        transitions_keys = reduce(set.union, [set(trans.keys()) for trans in self.transitions])
        func_decls_from_keys = {k.func for k in transitions_keys}
        return functions_initial | functions_cond_trans | func_decls_from_keys

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
        app = reduce(set.union, [utils.get_app(cond) for cond in self.conditions])
        return app

    def _get_app_from_transitions(self):
        app = set()
        for trans in self.transitions:
            trans_app = reduce(set.union, [utils.get_app(expr) for expr in trans.values()])
            app = app | trans_app 
        return app

    def _get_initial_func(self):
        return {app.func for app in self.initial if not app.is_Symbol}
