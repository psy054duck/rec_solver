import sympy as sp
from functools import reduce
import networkx as nx
import numpy as np
from sympy.core.function import UndefinedFunction
from sympy.parsing.sympy_parser import parse_expr, standard_transformations, convert_equals_signs
import z3
z3.set_option(max_depth=99999999)
# import cvc5.pythonic as z3

to_dnf = z3.Then(z3.With('simplify', elim_and=True), z3.Repeat(z3.OrElse(z3.Tactic('split-clause'), z3.Tactic('skip'))), 'ctx-solver-simplify')
# apply (then (! simplify :elim-and true) elim-term-ite tseitin-cnf))
to_cnf = z3.Then(z3.With('simplify', elim_and=True), z3.Tactic('elim-term-ite'), z3.Tactic('tseitin-cnf'))
coeff_idx = 0

class ConditionalExpr:
    def __init__(self, conds, exprs):
        self.conditions = conds
        self.expressions = exprs

    def add_case(self, cond, expr):
        self.conditions.append(cond)
        self.expressions.append(expr)

    def to_piecewise(self):
        res = list(zip([to_sympy(e) for e in self.expressions], [to_sympy(c) for c in self.conditions]))
        res[-1] = (res[-1][0], True)
        # return sp.Piecewise(*res)
        return sp.piecewise_fold(sp.Piecewise(*res))

def contains_function_symbols(expr):
    """
    Check if the given Z3 expression contains any function symbols.
    """
    if z3.is_app(expr):
        # Check if the expression is a function application
        decl = expr.decl()
        if decl.kind() == z3.Z3_OP_UNINTERPRETED and len(expr.children()) > 0:
            return True  # Found an uninterpreted function symbol
        # Recursively check all children
        for child in expr.children():
            if contains_function_symbols(child):
                return True
    return False

def get_applied_functions(expr):
    '''Get all applied functions without considering nesting'''
    if z3.is_app(expr):
        decl = expr.decl()
        if decl.kind() == z3.Z3_OP_UNINTERPRETED and len(expr.children()) > 0:
            return {expr}
    return reduce(set.union, [get_applied_functions(child) for child in expr.children()], set())


def ite2piecewise(cond, x, y):
    pieces = [(x, cond), (y, True)]
    return sp.Piecewise(*pieces)

def collapse_goal(goal):
    return z3.Or(*[z3.And(*clause) for clause in goal])

def simpliy_solver(e):
    e_z3 = to_z3(e)
    cases = to_dnf(e_z3)
    simplified_e_z3 = collapse_goal(cases)
    return to_sympy(simplified_e_z3)

def to_sympy(s_z3):
    # s = str(z3.simplify(s_z3, eq2ineq=True))
    s = str(z3.simplify(s_z3))
    expr = sp.parse_expr(s, local_dict={'If': ite2piecewise}, evaluate=False, transformations=(standard_transformations + (convert_equals_signs,)))
    if expr is True or expr is False:
        return sp.sympify(expr)
    symbols = expr.free_symbols
    symbols2int = {s: sp.Symbol(s.name, integer=True) for s in symbols}
    res = expr.subs(symbols2int, simultaneous=True)
    return res
    

def to_ite(piecewise):
    expr = piecewise[-1][0]
    for piece in reversed(piecewise[:-1]):
        expr = z3.If(piece[1], piece[0], expr)
    return expr


def is_linear(expr, terms):
    '''Check whether "expr" is linear in terms of "terms"'''
    for x in terms:
        for y in terms:
            try: 
                if not sp.Eq(sp.diff(expr, x, y), 0):
                    return False
            except TypeError:
                return False
    return True

# def get_app(expr):
#     '''Get applications (with symbolic arguments) and symbols from "expr"'''
#     try:
#         args = expr.args
#     except:
#         args = set()
#     if expr.is_number:
#         return set()
#     if (isinstance(expr.func, UndefinedFunction) and not any(arg.is_number for arg in args)) or expr.is_Symbol:
#         return {expr}
#     return reduce(set.union, [get_app(arg) for arg in args], set())

def get_app(expr):
    '''Get applications (with symbolic arguments) and symbols from "expr"'''
    try:
        args = expr.children()
    except:
        args = set()
    decl = expr.decl()
    if decl.kind() != z3.Z3_OP_UNINTERPRETED:
        return set()
    # if (isinstance(expr.func, UndefinedFunction) and not any(arg.is_number for arg in args)) or expr.is_Symbol:
    if any(arg.decl().kind() == z3.Z3_OP_UNINTERPRETED for arg in args):
        return {expr}
    return reduce(set.union, [get_app(arg) for arg in args], set())

def get_func_decls(expr):
    apps = get_app(expr)
    return {app.decl() for app in apps if app.decl().kind() == z3.Z3_OP_UNINTERPRETED}

def get_exponential_base_and_multiplicity(expr, ind_var):
    res = {}
    factors = _get_exponential_factors(expr, ind_var)
    factors_part = sp.Integer(0)
    for factor in factors:
        coeff = expr.coeff(factor)
        coeff_poly = coeff.as_poly([ind_var])
        res[factor.args[0]] = coeff_poly.total_degree() + 1
        factors_part = factors_part + expr.coeff(factor)*factor
    rest = sp.simplify(expr - factors_part).as_poly([to_sympy(ind_var)])
    res[sp.Integer(1)] = rest.total_degree() + 1
    return res

def _get_exponential_factors(expr, ind_var):
    if expr.is_number:
        return set()
    if expr.is_Pow and expr.args[0].is_number and ind_var in expr.args[1].free_symbols:
        return {expr}
    return reduce(set.union, (_get_exponential_factors(arg, ind_var) for arg in expr.args), set())

def split_linear_others(expr, functions, ind_var):
    '''For an expression of form Ax(n) + others, return (Ax(n), others)'''
    expr = sp.expand(to_sympy(expr))
    linear_part = sp.Integer(0)
    sp_functions = [to_sympy(f) for f in functions]
    for f in sp_functions:
        expr_poly = expr.as_poly(sp_functions)
        coeff = expr_poly.coeff_monomial(f)
        linear_part = linear_part + coeff*f
    ep = sp.simplify(expr - linear_part)
    return to_z3(linear_part), to_z3(ep)

def sorted_strong_ly_connected_components(matrix):
    G = nx.DiGraph(np.array(matrix.tolist(), dtype=int))
    # components = list(nx.strongly_connected_components(G))
    condensed = nx.condensation(G)
    sorted_condensed = list(reversed(list(nx.topological_sort(condensed))))
    components = [condensed.nodes.data()[i]['members'] for i in sorted_condensed]
    return components

def compress_seq(seq):
    return _compress_seq(seq, [], None)

def _compress_seq(seq, cur_compressed, best_compressed):
    covered_seq = sum([pattern*cnt for pattern, cnt in cur_compressed], [])
    remaining_seq = seq[len(covered_seq):]
    if best_compressed is not None:
        cur_compressed_ratio = compressed_ratio(seq, cur_compressed)
        best_compressed_ratio = compressed_ratio(seq, best_compressed)
        if best_compressed_ratio >= cur_compressed_ratio:
            return best_compressed
    if len(remaining_seq) == 0:
        return cur_compressed
    if len(remaining_seq) == 1:
        return cur_compressed + [(seq, 1)]
    if best_compressed is None:
        cur_best_compressed = (cur_compressed + [(seq, 1)])
    else:
        cur_best_compressed = best_compressed
    best_ratio = compressed_ratio(seq, cur_best_compressed)
    for window in range(1, len(remaining_seq)//2 + 1):
        pattern = remaining_seq[:window]
        cnt = 1
        while pattern*cnt == remaining_seq[:len(pattern)*cnt]:
            cnt += 1
        candidate_compressed = _compress_seq(seq, cur_compressed + [(pattern, cnt - 1)], cur_best_compressed)
        cur_ratio = compressed_ratio(seq, candidate_compressed)
        if cur_ratio > best_ratio:
            cur_best_compressed = candidate_compressed
            best_ratio = cur_ratio
    return cur_best_compressed

def compressed_ratio(seq, compressed):
    return len(seq) / sum((len(pattern) for pattern, _ in compressed))

def pow_to_mul(expr):
    """
    Convert integer powers in an expression to Muls, like a**2 => a*a.
    """
    pows = list(expr.atoms(sp.Pow))
    if any(not e.is_Integer for _, e in (i.as_base_exp() for i in pows)):
        if any(b != -1 for b, _ in (p.as_base_exp() for p in pows)):
            raise ValueError("A power contains a non-integer exponent")
    #repl = zip(pows, (Mul(*list([b]*e for b, e in i.as_base_exp()), evaluate=False) for i in pows))
    repl = zip(pows, (sp.Mul(*[b]*e, evaluate=False) if b != -1 else sp.Piecewise((1, sp.Eq(e % 2, 0)), (-1, True)) for b,e in (i.as_base_exp() for i in pows)))
    return expr.subs(repl), list(repl)

def to_z3(sp_expr, sort='int'):
    self = sp.factor(sp_expr)
    self, repl = pow_to_mul(self)
    if sort == 'int':
        func_arg_sort = z3.IntSort()
    elif sort == 'real':
        func_arg_sort = z3.RealSort()
    else:
        raise Exception('unsupported sort %s' % sort)
    if isinstance(self, sp.Add):
        res = sum([to_z3(arg, sort) for arg in self.args])
    elif isinstance(self, sp.Mul):
        res = 1
        for arg in reversed(self.args):
            if arg.is_number and not arg.is_Integer:
                try:
                    res = (res*arg.numerator())/arg.denominator()
                except:
                    res = (res*arg.numerator)/arg.denominator
            else:
                res = res * to_z3(arg, sort)
        return z3.simplify(res)
        # return reduce(lambda x, y: x*y, [to_z3(arg) for arg in reversed(self.args)])
    elif isinstance(self, sp.Piecewise):
        if len(self.args) == 1:
            res = to_z3(self.args[0][0], sort)
        else:
            cond  = to_z3(self.args[0][1], sort)
            res = z3.If(cond, to_z3(self.args[0][0], sort), to_z3(self.args[1][0], sort))
    elif isinstance(self, sp.And):
        res = z3.And(*[to_z3(arg, sort) for arg in self.args])
    elif isinstance(self, sp.Or):
        res = z3.Or(*[to_z3(arg, sort) for arg in self.args])
    elif isinstance(self, sp.Not):
        res = z3.Not(*[to_z3(arg, sort) for arg in self.args])
    elif isinstance(self, sp.Gt):
        res = to_z3(self.lhs, sort) > to_z3(self.rhs, sort)
    elif isinstance(self, sp.Ge):
        res = to_z3(self.lhs, sort) >= to_z3(self.rhs, sort)
    elif isinstance(self, sp.Lt):
        res = to_z3(self.lhs, sort) < to_z3(self.rhs, sort)
    elif isinstance(self, sp.Le):
        res = to_z3(self.lhs, sort) <= to_z3(self.rhs, sort)
    elif isinstance(self, sp.Eq):
        res = to_z3(self.lhs, sort) == to_z3(self.rhs, sort)
    elif isinstance(self, sp.Ne):
        res = to_z3(self.lhs, sort) != to_z3(self.rhs, sort)
    elif isinstance(self, sp.Integer) or isinstance(self, int):
        res = z3.IntVal(int(self))
    elif isinstance(self, sp.Symbol):
        if sort == 'int':
            res = z3.Int(str(self))
        elif sort == 'real':
            res = z3.Real(str(self))
    elif isinstance(self, sp.Rational):
        # return z3.RatVal(self.numerator, self.denominator)
        res = z3.IntVal(self.numerator) / z3.IntVal(self.denominator)
    elif isinstance(self, sp.ITE):
        res = z3.If(to_z3(self.args[0]), to_z3(self.args[1]), to_z3(self.args[2]))
    elif isinstance(self, sp.Pow):
        if self.base == 0: res = z3.IntVal(0)
        else: raise Exception('%s' % self)
    elif isinstance(self, sp.Mod):
        res = to_z3(self.args[0], sort) % to_z3(self.args[1], sort)
    elif isinstance(self, sp.Abs):
        res = z3.Abs(to_z3(self.args[0]), sort)
    elif isinstance(self, sp.Sum):
        s = z3.Function('Sum', z3.IntSort(), z3.IntSort(), z3.IntSort(), z3.IntSort(), z3.IntSort())
        # expr, (idx, start, end) = self.args
        expr, *l = self.args
        res = to_z3(expr, sort)
        for idx, start, end in l:
            res = s(res, to_z3(idx, sort), to_z3(start, sort), to_z3(end, sort))
    elif self is sp.true:
        res = z3.BoolVal(True)
    elif self is sp.false:
        res = z3.BoolVal(False)
    elif self.is_Function:
        func = self.func
        args = self.args
        z3_func = z3.Function(func.name, *([func_arg_sort]*(len(args) + 1)))
        res = z3_func(*[to_z3(arg, sort) for arg in args])
    else:
        raise Exception('Conversion for "%s" has not been implemented yet: %s' % (type(self), self))
    return z3.simplify(res)

def interval_to_z3(interval, ind_var):
    ind_var_z3 = to_z3(ind_var)
    left = to_z3(interval.left)
    right = None if interval.right is sp.oo else to_z3(interval.right)
    cond = left <= ind_var_z3 if right is None else z3.And(left <= ind_var_z3, ind_var_z3 < right)
    return cond

def compute_q(constraint, q, vars, ind_var):
    '''q is constrained by constraint. Express q as linear combination of other variables in constraint. If it is not linear raise error'''
    res = to_z3(compute_piecewise_q(constraint, q, vars, ind_var))
    try:
        res = to_z3(compute_piecewise_q(constraint, q, vars, ind_var))
        return res
    except:
        pass
    variables = [to_z3(v) for v in vars]
    q_z3 = to_z3(q)
    cs = [z3.Int('__c%d' % i) for i in range(len(variables) + 1)]
    template = sum([c*v for c, v in zip(cs, variables)]) + cs[-1]

    eq_solver = z3.Solver()
    constraint_solver = z3.Solver()
    # constraint_solver.add(q_z3 >= 1)
    points = []
    full_constraint = z3.ForAll(ind_var, z3.Implies(ind_var >= 0, constraint))
    constraint_solver.push()
    for _ in range(len(cs)):
        if constraint_solver.check(full_constraint) == z3.unsat: break
        m = constraint_solver.model()
        point = [m.eval(var, True) for var in variables]
        eq_solver.add(m.eval(q_z3, True) == z3.substitute(template, *list(zip(variables, point))))
        points.append(point)
        ls = [z3.Real('__l%d' % i) for i in range(len(points))]
        if point == [0]*len(point):
            constraint_solver.add(z3.Or(*[var != 0 for var in variables]))
        else:
            vec_space = []
            for i, var in enumerate(variables):
                vec_space.append(var == sum(p[i]*ls[j] for j, p in enumerate(points)))
            constraint_solver.add(z3.Not(z3.Exists(ls, z3.And(*vec_space))))
    constraint_solver.pop()
    eq_solver.check()
    m = eq_solver.model()
    linear_expr = z3.substitute(template, *[(c, m.eval(c, True)) for c in cs])
    res = constraint_solver.check(q_z3 != linear_expr, full_constraint)
    if res == z3.sat:
        return None
    return z3.simplify(linear_expr)

def compute_piecewise_q(constraint, q, vars, ind_var):
    variables = [to_z3(v) for v in vars]
    q_z3 = to_z3(q)
    num_coeffs = len(variables) + 1
    post_cs1 = [z3.Int('__c%d' % i) for i in range(num_coeffs)]
    post_cs2 = [z3.Int('__c%d' % i) for i in range(num_coeffs, 2*num_coeffs)]
    post_template1 = sum([c*v for c, v in zip(post_cs1, variables)]) + post_cs1[-1]
    post_template2 = sum([c*v for c, v in zip(post_cs2, variables)]) + post_cs2[-1]

    constraint_solver = z3.Solver()
    # constraint_solver.add(q_z3 >= 1)
    points = []
    full_constraint = z3.ForAll(ind_var, z3.Implies(ind_var >= 0, constraint))
    # res = constraint_solver.check(z3.ForAll(variables + [q_z3], z3.Implies(full_constraint, z3.Or(q_z3 == post_template1, q_z3 == post_template2))))
    qe = z3.Then(z3.Tactic('qe'), z3.Tactic('ctx-solver-simplify'))
    qe_constraints = qe.apply(full_constraint)
    # print(qe_constraint)
    # print(sp.simplify(to_sympy(full_constraint)))
    set_cons = set()
    # for con in qe_constraints[0]:
    #     print(con)
    # print('^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^')
    for c in qe_constraints[0]:
        set_cons = set_cons.union(sp.simplify(to_sympy(c)).atoms(sp.Eq, sp.Ge, sp.Gt, sp.Le, sp.Lt))
    
    # set_eq_containing_q = {eq for eq in set_eq if len(eq.atoms(q)) != 0}
    set_eq = {sp.Eq(a.lhs, a.rhs) for a in set_cons}
    set_eq_containing_q = {eq for eq in set_eq if q in eq.atoms(sp.Symbol)}
    assert(all(sp.Poly(eq, *(vars | {q})).is_linear for eq in set_eq_containing_q))
    q_linear_exprs = []
    for eq in set_eq_containing_q:
        expr_list = sp.solve(eq, q, list=True)
        all_expr_list = expr_list + [e - 1 for e in expr_list] + [e + 1 for e in expr_list]
        q_linear_exprs.extend(all_expr_list)
    solver = z3.Solver()
    q_eqs = sp.Or(*[sp.Eq(q, expr) for expr in q_linear_exprs])
    qe_constraint = z3.And(*qe_constraints[0])
    res = solver.check(z3.ForAll(variables + [q_z3], z3.And(qe_constraint, z3.Not(to_z3(q_eqs)))))
    conds = []
    sim = z3.Then(z3.Tactic('ctx-solver-simplify'), z3.Tactic('simplify'), z3.Tactic('ctx-solver-simplify'))
    if res == z3.unsat:
        for expr in q_linear_exprs:
            cond = z3.substitute(qe_constraint, (q_z3, to_z3(expr)))
            conds.append(z3.And(*sim(cond)[0]))
    pieces = []
    for cond, expr in zip(conds, q_linear_exprs):
        cond_sp = to_sympy(cond)
        if cond_sp is not sp.false:
            pieces.append((expr, to_sympy(cond)))
    pieces[-1] = (pieces[-1][0], True)
    return sp.Piecewise(*pieces)

def is_same_transition(trans1, trans2):
    if set(trans1.keys()) != set(trans2.keys()):
        return False
    return all([sp.simplify(sp.Eq(trans1[k], trans2[k])) for k in trans1])

def flatten_seq(seq):
    return sum([l*c for l, c in seq], [])

def solve_piecewise_sol(constraint, x, sort=z3.Real):
    dnf = to_dnf(constraint)
    solver = z3.Solver()
    premises = []
    linear_exprs = []
    for conjunct in dnf:
        formula = z3.And(*conjunct)
        # try:
        linear_expr = _solve_linear_expr_heuristic(conjunct, x)
        # except:
        #     linear_expr = None
        if linear_expr is None:
            all_vars = [var.n for var in get_vars(formula)]
            vars = [var for var in all_vars if str(var) != str(x)] + [1]
            coeffs = [sort('_c%d' % i) for i in range(len(vars))]
            linear_template = sum([c*v for c, v in zip(coeffs, vars)])
            res = solver.check(z3.ForAll(all_vars, z3.Implies(formula, x == linear_template)))
            if res == z3.sat:
                m = solver.model()
                linear_expr = m.eval(linear_template)
        if linear_expr is not None:
            linear_exprs.append(linear_expr)
            premises.append(z3.simplify(z3.substitute(formula, (x, linear_expr))))
        else:
            return None
    return ConditionalExpr(premises, linear_exprs)
    # return _pack_piecewise_sol(premises[:-1], linear_exprs)

def _solve_linear_expr_heuristic(constraints, x):
    '''Assume constraints is a list of formulas, representing a conjunction.
       Compute x as a linear expression of other variables heuristically'''
    # all_vars = [var.n for var in get_vars(z3.And(*constraints)) ]
    possible_exprs = _get_possible_exprs(constraints, x)
    solver = z3.Solver()
    for expr in possible_exprs:
        res = solver.check(z3.And(z3.And(*constraints), z3.Not(x == to_z3(expr))))
        if res == z3.unsat:
            return to_z3(expr)
    return None

def _get_possible_exprs(constraints, x):
    possible_formulas = []
    for formula in constraints:
        all_vars = get_vars(formula)
        if str(x) in [str(var) for var in all_vars]:
            possible_formulas.append(formula)
    # convert them into equations
    possible_formulas_sp = [to_sympy(formula) for formula in possible_formulas]
    possible_formulas_sp = [formula for formula in possible_formulas_sp if not isinstance(formula, sp.And)]\
                         + sum([list(formula.args) for formula in possible_formulas_sp if isinstance(formula, sp.And)], [])
    possible_eqs = [sp.Eq(f.lhs, f.rhs) for f in possible_formulas_sp]\
                 + [sp.Eq(f.lhs, f.rhs + 1) for f in possible_formulas_sp]\
                 + [sp.Eq(f.lhs, f.rhs - 1) for f in possible_formulas_sp]
    res = []
    for eq in possible_eqs:
        res.extend(sp.solve(eq, to_sympy(x), list=True))
    return res

def _pack_piecewise_sol(premises, conclusions):
    k = len(conclusions)
    if k == 1:
        res = conclusions[0]
    else:
        res = z3.If(premises[-1], conclusions[-2], conclusions[-1])
    for i in range(k - 2):
        idx = k - 3 - i
        res = z3.If(premises[idx], conclusions[idx], res)
    return res

def gen_piecewise_template_components(vars, x, k, sort=z3.Real):
    '''generate piecewise template over vars with k branches'''
    global coeff_idx
    extended_vars = vars + [1]
    num_vars = len(extended_vars)
    # generate premises
    premises = []
    conclusions = []
    for i in range(k - 1):
        linear_exprs = gen_template_linear(extended_vars, k)
        premises.append(z3.And(*[expr >= 0 for expr in linear_exprs]))
        coeffs = [sort('_c%d' % j) for j in range(coeff_idx + num_vars*i, coeff_idx + num_vars*(i + 1))]
        coeff_idx += len(coeffs)
        conclusion = gen_template_linear(extended_vars, 1)[0]
        conclusions.append(conclusion)
    # generate conclusion
    coeffs = [sort('_c%d' % j) for j in range(coeff_idx + num_vars*(k - 1), coeff_idx + num_vars*k)]
    coeff_idx += len(coeffs)
    conclusion = gen_template_linear(extended_vars, 1)[0]
    conclusions.append(conclusion)
    return premises, conclusions

def pack_piecewise_components(premises, conclusions):
    acc_pre = z3.BoolVal(True)
    implications = []
    for pre, con in zip(premises, conclusions):
        implications.append(z3.Implies(z3.And(acc_pre, pre), con))
        acc_pre = z3.And(acc_pre, z3.Not(pre))
    implications.append(z3.Implies(acc_pre, conclusions[-1]))
    return z3.And(*implications)

def gen_template_linear(vars, k, sort=z3.Real):
    '''Generate template linear expression over vars with coeffs as template coefficients'''
    global coeff_idx
    linear_exprs = []
    for _ in range(k):
        coeffs = [sort('_c%d' % j) for j in range(coeff_idx, coeff_idx + len(vars))]
        coeff_idx += len(coeffs)
        linear_exprs.append(sum([var*c for var, c in zip(vars, coeffs)], z3.RealVal(0)))
    return linear_exprs

################################### This part is copied from stackoverflow ###################
# This part is for getting all variables appearing in a z3 formula
# use get_vars(f) to get all variables in f
# class _AstRefKey:
#     def __init__(self, n):
#         self.n = n
#     def __hash__(self):
#         return self.n.hash()
#     def __eq__(self, other):
#         return self.n.eq(other.n)
#     def __repr__(self):
#         return str(self.n)
# 
# def _askey(n):
#     assert isinstance(n, z3.AstRef)
#     return _AstRefKey(n)

def get_vars(f: z3.ExprRef):
    '''f: a formula in z3
       ret: set of all variables in f'''
    r = set()
    def collect(f):
      if z3.is_const(f): 
          if f.decl().kind() == z3.Z3_OP_UNINTERPRETED:
              r.add(f)
      else:
          for c in f.children():
              collect(c)
    collect(f)
    return r
################################################################################################

if __name__ == '__main__':
    # x, y, z, q = z3.Ints('x y z q')
    # constraint = z3.Or(z3.And(q >= x + y, q <= x + y, x > 0, y > 0), z3.And(q >= 2*x, q <= 2*x, z3.Or(x <= 0, y <= 0)))
    # res = solve_piecewise_sol(constraint, q)
    # print(res)
    q0, k, z, c, _d = z3.Ints('q0 k z c _d')
    from z3 import If, Or, And, Not
    e1 = If(Or(And(1 <= z, Not(0 <= c)), And(-1 == c, 1 <= z, Not(0 <= c)), And(1 <= z, Not(c <= -1), Not(c + -1*z <= -1))), z, -1 + z + -1*c) <= _d
    e2 = Or(And(1 <= z, Not(0 <= c)), And(-1 == c, 1 <= z, Not(0 <= c)), And(1 <= z, Not(c <= -1), Not(c + -1*z <= -1)))
    dnf = z3.Then(to_cnf, to_dnf)
    print(e1)
    print(dnf(e1))
    print(e2)
    print(dnf(e2))
    # sim = z3.Then(z3.Tactic('simplify'), z3.Tactic('solve-eqs'), z3.Tactic('ctx-solver-simplify'))
    # print(z3.simplify(z3.Or(*[z3.And(*conjunct) for conjunct in sim(e1)])))
    # print(z3.simplify(z3.Or(*[z3.And(*conjunct) for conjunct in sim(e2)])))
    # qe = z3.Tactic('qe')
    # print(qe(z3.ForAll(k, z3.And(q >= 1, z3.Implies(z3.And(0 <= k, k < q), z3.And(k < z, k + z - c - 1 != 0))))))
    # from z3 import And, Implies, Not, ForAll, Or
    # # e = And(And(And(True, Implies(Not(q0 <= 1*k + 0), And(Not(z + -1*(1*k + 0) <= 0), Not(-1 == -1*(z + -1*(1*k + 0)) + c)))), Implies(q0 <= 1*k + 0, And(Not(z + -1*q0 <= 0), -1 == -1*(z + -1*q0) + c))), q0 >= 1)
    # # e = And(And(True, Implies(Not(q0 <= 1*k + 0), And(Not(z + -1*(1*k + 0) <= 0), Not(-1 == -1*(z + -1*(1*k + 0)) + c)))), Implies(q0 <= 1*k + 0, And(Not(And(Not(z + -1*q0 <= 0), -1 == -1*(z + -1*q0) + c)), Not(And(Not(z + -1*q0 <= 0), Not(-1 == -1*(z + -1*q0) + c))))))
    # # e = And(q0 >= 1, Not(z + -1*q0 <= 0), -1 == -1*z + q0 + c, Not(And(c + -1*z <= -1, Or(Not(q0 >= 1), And(q0 + c + -1*z <= -1, Not(And(Not(z + -1*q0 <= 0), -1 == -1*z + q0 + c))), -1*q0 + -1*c + z <= 0))), Not(And(q0 >= 1, Or(Not(q0 >= 1), z + -1*q0 <= -1, And(-1*c + z + -1*q0 <= 0, c + -1*z + q0 <= -1)))))
    # e = And(Not(And(Not(z + -1*q0 <= 0), Not(-1 == -1*z + q0 + c))), q0 >= 1, Not(And(c + -1*z <= -1, Or(Not(q0 >= 1), -1*q0 + -1*c + z <= 0, And(q0 + c + -1*z <= -1, Not(z + -1*q0 <= 0), Not(-1 == -1*z + q0 + c))))), Not(And(q0 >= 1, Or(Not(q0 >= 1), z + -1*q0 <= -1, And(-1*c + z + -1*q0 <= 0, c + -1*z + q0 <= -1)))))
    # q = solve_piecewise_sol(e, q0, z3.Int)
    # print(q)
    # sim = z3.With(z3.Tactic('simplify'), eq2ineq=True)
    # print(sim(e))
    # solver = z3.Solver()
    # # res = solver.check(And(ForAll(k, Implies(k >= 0, e)), Not(q0 == z), q0 >= 1))
    # # res = solver.check(And(ForAll(k, Implies(k >= 0, e)), Not(q0 == z - c - 1), q0 >= 1))
    # res = solver.check(And(e, Not(q0 == z - c - 1), q0 >= 1))
    # print(res)
    # print(solver.model())
