import sympy as sp
from functools import reduce
import networkx as nx
import numpy as np
from sympy.core.function import UndefinedFunction
import z3
# import cvc5.pythonic as z3

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

def get_app(expr):
    '''Get applications (with symbolic arguments) and symbols from "expr"'''
    try:
        args = expr.args
    except:
        args = set()
    if expr.is_number:
        return set()
    if (isinstance(expr.func, UndefinedFunction) and not any(arg.is_number for arg in args)) or expr.is_Symbol:
        return {expr}
    return reduce(set.union, [get_app(arg) for arg in args], set())

def get_func_decls(expr):
    apps = get_app(expr)
    return {app.func for app in apps if not app.is_number}

def get_exponential_base_and_multiplicity(expr, ind_var):
    res = {}
    factors = _get_exponential_factors(expr, ind_var)
    factors_part = sp.Integer(0)
    for factor in factors:
        coeff = expr.coeff(factor)
        coeff_poly = coeff.as_poly([ind_var])
        res[factor.args[0]] = coeff_poly.total_degree() + 1
        factors_part = factors_part + expr.coeff(factor)*factor
    rest = sp.simplify(expr - factors_part).as_poly([ind_var])
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
    expr = sp.expand(expr)
    linear_part = sp.Integer(0)
    for f in functions:
        expr_poly = expr.as_poly(functions)
        coeff = expr_poly.coeff_monomial(f)
        linear_part = linear_part + coeff*f
    ep = sp.simplify(expr - linear_part)
    return linear_part, ep

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

def to_z3(sp_expr):
    self = sp.factor(sp_expr)
    self, repl = pow_to_mul(self)
    if isinstance(self, sp.Add):
        res = sum([to_z3(arg) for arg in self.args])
    elif isinstance(self, sp.Mul):
        res = 1
        for arg in reversed(self.args):
            if arg.is_number and not arg.is_Integer:
                try:
                    res = (res*arg.numerator())/arg.denominator()
                except:
                    res = (res*arg.numerator)/arg.denominator
            else:
                res = res * to_z3(arg)
        return z3.simplify(res)
        # return reduce(lambda x, y: x*y, [to_z3(arg) for arg in reversed(self.args)])
    elif isinstance(self, sp.Piecewise):
        if len(self.args) == 1:
            res = to_z3(self.args[0][0])
        else:
            cond  = to_z3(self.args[0][1])
            res = z3.If(cond, to_z3(self.args[0][0]), to_z3(self.args[1][0]))
    elif isinstance(self, sp.And):
        res = z3.And(*[to_z3(arg) for arg in self.args])
    elif isinstance(self, sp.Or):
        res = z3.Or(*[to_z3(arg) for arg in self.args])
    elif isinstance(self, sp.Not):
        res = z3.Not(*[to_z3(arg) for arg in self.args])
    elif isinstance(self, sp.Gt):
        res = to_z3(self.lhs) > to_z3(self.rhs)
    elif isinstance(self, sp.Ge):
        res = to_z3(self.lhs) >= to_z3(self.rhs)
    elif isinstance(self, sp.Lt):
        res = to_z3(self.lhs) < to_z3(self.rhs)
    elif isinstance(self, sp.Le):
        res = to_z3(self.lhs) <= to_z3(self.rhs)
    elif isinstance(self, sp.Eq):
        res = to_z3(self.lhs) == to_z3(self.rhs)
    elif isinstance(self, sp.Ne):
        res = to_z3(self.lhs) != to_z3(self.rhs)
    elif isinstance(self, sp.Integer) or isinstance(self, int):
        res = z3.IntVal(int(self))
    elif isinstance(self, sp.Symbol):
        res = z3.Int(str(self))
    elif isinstance(self, sp.Rational):
        # return z3.RatVal(self.numerator, self.denominator)
        res = z3.IntVal(self.numerator) / z3.IntVal(self.denominator)
    elif isinstance(self, sp.Pow):
        if self.base == 0: res = z3.IntVal(0)
        else: raise Exception('%s' % self)
    elif isinstance(self, sp.Mod):
        res = to_z3(self.args[0]) % to_z3(self.args[1])
    elif isinstance(self, sp.Abs):
        res = z3.Abs(to_z3(self.args[0]))
    elif isinstance(self, sp.Sum):
        s = z3.Function('Sum', z3.IntSort(), z3.IntSort(), z3.IntSort(), z3.IntSort(), z3.IntSort())
        # expr, (idx, start, end) = self.args
        expr, *l = self.args
        res = to_z3(expr)
        for idx, start, end in l:
            res = s(res, to_z3(idx), to_z3(start), to_z3(end))
    elif self is sp.true:
        res = z3.BoolVal(True)
    elif self is sp.false:
        res = z3.BoolVal(False)
    elif self.is_Function:
        func = self.func
        args = self.args
        z3_func = z3.Function(func.name, *([z3.IntSort()]*(len(args) + 1)))
        res = z3_func(*[to_z3(arg) for arg in args])
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
        constraint_solver.check(full_constraint)
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
    return linear_expr
