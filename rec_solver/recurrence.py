import sympy as sp
from sympy.core.function import AppliedUndef
from . import utils
from functools import reduce
from collections import defaultdict

class Recurrence:
    def __new__(cls, branches):
        base_conditions, base_transitions, recursive_conditions, recursive_transitions = Recurrence.divide_to_base_and_recursive(branches)
        if Recurrence.is_loop_recurrence(branches):
            ind_var = Recurrence.get_possible_ind_var(recursive_transitions)
            assert(len(base_transitions) == 1)
            base_transition = base_transitions[0]
            initial = {f.subs({ind_var: 0}, simultaneous=True): base_transition[f] for f in base_transition}
            new_branches = list(zip(recursive_conditions, recursive_transitions))
            return LoopRecurrence(initial, new_branches)
        else:
            random_rec_case = recursive_transitions[0]
            func_sig = list(random_rec_case.keys())[0]
            return MultiRecurrence(branches)

    @staticmethod
    def divide_to_base_and_recursive(branches):
        base_conditions = []
        recursive_conditions = []
        base_transitions = []
        recursive_transitions = []
        for cond, trans in branches:
            if Recurrence.is_base_condition(cond) and Recurrence.is_base_transition(trans):
                base_conditions.append(cond)
                base_transitions.append(trans)
            else:
                recursive_conditions.append(cond)
                recursive_transitions.append(trans)
        return base_conditions, base_transitions, recursive_conditions, recursive_transitions

    @staticmethod
    def is_base_condition(cond):
        return len(cond.atoms(AppliedUndef)) == 0

    @staticmethod
    def is_base_transition(trans):
        return all([len(e.atoms(AppliedUndef)) == 0 for e in trans.values()])

    @staticmethod
    def is_loop_recurrence(branches):
        conditions = [branch[0] for branch in branches]
        transitions = [branch[1] for branch in branches]
        for cond, trans in zip(conditions, transitions):
            applied_func = cond.atoms(AppliedUndef)
            # applied_func |= reduce(set.union, [set(trans.keys()) | set(trans.values()) for trans in trans])
            applied_func |= reduce(set.union, [e.atoms(AppliedUndef) for e in trans.keys()])
            applied_func |= reduce(set.union, [e.atoms(AppliedUndef) for e in trans.values()])
            # applied_func |= set(trans.keys()) | set(trans.values())
            # check if all functions are univariate
            if not all([list(f.nargs)[0] == 1 for f in applied_func]):
                return False
            # check if the inductive variable is the only symbol in arguments
            ind_var = Recurrence.get_possible_ind_var(transitions)
            args = reduce(set.union, [set(f.args) for f in applied_func])
            if not all([len(arg.free_symbols) == 1 for arg in args]) and not all([list(arg.free_symbols)[0] == ind_var for arg in args]):
                return False
            # check if all recursive cases are of form f(n + 1) = g(f(n))
            if not all([arg - ind_var == 0 or arg - ind_var - 1 == 0 for arg in args]):
                return False
        return True

    @staticmethod
    def make_exclusive_conditions(conditions):
        acc_neg = sp.true
        exclusive_conditions = []
        for cond in conditions:
            exclusive_conditions.append(sp.simplify(sp.And(acc_neg, cond)))
            acc_neg = sp.And(acc_neg, sp.Not(cond))
        if sp.simplify(acc_neg) != sp.false:
            exclusive_conditions.append(acc_neg)
        return exclusive_conditions

    @staticmethod
    def get_initial(conditions, transitions, ind_var):
        '''get the initial values if the recurrence is from a loop'''
        assert(Recurrence.is_loop_recurrence(conditions, transitions))
        for cond, trans in zip(conditions, transitions):
            if Recurrence.is_base_condition(cond) and Recurrence.is_base_transition(trans):
                # assume cond is of form n == 0, where 'n' is the loop counter and c is a constant
                initial = {f.subs({ind_var: 0}): trans[f] for f in trans}
                break
        else:
            raise Exception('there is no base case')
        return initial

    @staticmethod
    def get_possible_ind_var(transitions):
        '''treat the only symbol in the first argument as the inductive variable'''
        first_trans = transitions[0]
        first_applied_func = list(first_trans.keys())[0]
        first_arg = first_applied_func.args[0]
        return list(first_arg.free_symbols)[0]

class MultiRecurrence:
    def __init__(self, *args):
        if isinstance(args[0], list):
            branches = args[0]
            conditions = [branch[0] for branch in branches]
            self._conditions = Recurrence.make_exclusive_conditions(conditions)
            self._transitions = [branch[1] for branch in branches]
            self.func_sig = list(self.transitions[0].keys())[0]
            # for the recursive case,
            # an operation should consists of dictionary of recursive calls
            # followed by an linear transformation on them,
            # whose result is the returned value for this case.
            self.recursive_calls, self.post_ops = self._preprocess_transitions(self.transitions)
        else:
            self.func_sig, self._conditions, self._transitions, self.recursive_calls, self.post_ops = args

    def number_ret(self):
        return len(self.post_ops[0])

    def subs(self, mapping):
        func_sig = self.func_sig.subs(mapping, simultaneous=True)
        conditions  = [cond.subs(mapping, simultaneous=True) for cond in self.conditions]
        transitions = []
        for transition in self.transitions:
            transitions.append({k.subs(mapping, simultaneous=True): t.subs(mapping, simultaneous=True) for k, t in transition.items()})
        recursive_calls = []
        for call in self.recursive_calls:
            recursive_calls.append({k: call[k].subs(mapping, simultaneous=True) for k in call})
        return MultiRecurrence(func_sig, conditions, transitions, recursive_calls, self.post_ops)

    @property
    def conditions(self):
        return self._conditions.copy()

    @property
    def transitions(self):
        return self._transitions.copy()

    def _preprocess_transitions(self, transitions):
        recursive_calls = []
        post_ops = []
        for trans in transitions:
            assert(len(trans.keys()) == 1)
            rhs = list(trans.values())[0]
            func_apps = list(rhs.atoms(self.func_sig))
            named_calls = {sp.Symbol('a%d' % i, integer=True): func_apps[i] for i in range(len(func_apps))}
            call_names = {func_apps[i]: sp.Symbol('a%d' % i, integer=True) for i in range(len(func_apps))}
            post_op = rhs.subs(call_names, simultaneous=True)
            recursive_calls.append(named_calls)
            post_ops.append((post_op,))
        return recursive_calls, post_ops

    def sympify(self):
        exp = defaultdict(list)
        for cond, trans in zip(self.conditions, self.transitions):
            for f in trans:
                exp[f].append((trans[f], cond))
        return {f: sp.Piecewise(*exp[f]) for f in exp}


    def pprint(self):
        sp.init_printing()
        rec_sym = self.sympify()
        for f in rec_sym:
            sp.pprint(sp.Eq(f, rec_sym[f]))
            print()

    def is_nearly_tail(self):
        return all([len(set(calls.values())) <= 1 for calls in self.recursive_calls])

    def get_base_cases(self):
        conditions, _, post_ops = self._get_cases()
        return conditions, post_ops

    def get_rec_cases(self):
        return self._get_cases(False)

    def _get_cases(self, is_base=True):
        p = lambda calls: len(calls) == 0
        if not is_base:
             p = lambda calls: len(calls) > 0
        conditions = []
        recursive_calls = []
        post_ops = []
        for i, rec_calls in enumerate(self.recursive_calls):
            if p(rec_calls):
                conditions.append(self.conditions[i])
                recursive_calls.append(self.recursive_calls[i])
                post_ops.append(self.post_ops[i])
        return conditions, recursive_calls, post_ops

    def is_base_condition(self, cond):
        func_apps = cond.atoms(self.func_sig)
        return len(func_apps) == 0

    def is_base_transition(self, trans):
        for f in trans:
            func_apps = trans[f].atoms(self.func_sig)
            if len(func_apps) > 0:
                return False
        return True

class LoopRecurrence:
    def __init__(self, initial, branches):
        self._preprocess(initial, branches)
        self.cached_result = {}

    def _preprocess(self, initial, branches):
        conditions = [branch[0] for branch in branches]
        self._conditions = Recurrence.make_exclusive_conditions(conditions)
        self._transitions = [branch[1] for branch in branches]
        if len(self._conditions) > len(conditions):
            self._transitions = [branch[1] for branch in branches] + [{}]
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

    # def __init__(self, branches):
    #     self._base_conditions = []
    #     self._recursive_conditions = []
    #     self._base_transitions = []
    #     self._recursive_transitions = []
    #     for cond, trans in branches:
    #         if self.is_base_case(cond, trans):
    #             self._base_conditions.append(cond)
    #             self._base_transitions.append(trans)
    #         else:
    #             self._recursive_conditions.append(cond)
    #             self._recursive_transitions.append(trans)
        
    @staticmethod
    def mk_rec(initial, conditions, transitions):
        branches = list(zip(conditions, transitions))
        return LoopRecurrence(initial, branches)

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
        return LoopRecurrence(initial, branches)

    def copy_rec_with_diff_initial(self, new_initial):
        branches = list(zip(self.conditions, self.transitions))
        return LoopRecurrence(new_initial, branches)



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
        return len(self.get_symbolic_values()) == 0 and all([e.is_number for e in self.initial.values()]) and all((func_decl(0) in self.initial for func_decl in self.func_decls))

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

    # @property
    # def base_conditions(self):
    #     return self._base_conditions.copy()

    # @property
    # def base_transitions(self):
    #     return self._base_transitions.copy()

    # @property
    # def recursive_conditions(self):
    #     return self._recursive_conditions.copy()

    # @property
    # def recursive_transitions(self):
    #     return self._recursive_transitions.copy()

    @property
    def conditions(self):
        return self._conditions.copy()
        # return self.base_conditions + self.recursive_conditions

    @property
    def transitions(self):
        return self._transitions.copy()
        # return self.base_transitions + self.recursive_transitions

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
            trans_app = reduce(set.union, [utils.get_app(expr) for expr in trans.values()], set())
            app = app | trans_app 
        return app

    def _get_initial_func(self):
        return {app.func for app in self.initial if not app.is_Symbol}

    def sympify(self):
        exp = defaultdict(list)
        for cond, trans in zip(self.conditions, self.transitions):
            for f in trans:
                exp[f].append((trans[f], cond))
        return {f: sp.Piecewise(*exp[f]) for f in exp}

    def pprint(self):
        sp.init_printing()
        rec_sym = self.sympify()
        for f in self.initial:
            sp.pprint(sp.Eq(f, self.initial[f]))
        print()
        for f in rec_sym:
            sp.pprint(sp.Eq(f, rec_sym[f]))
            print()

