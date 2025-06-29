from z3 import *
import z3
from typing import Optional
'''This module contains the logic simplification functions.'''

import z3
from itertools import product

def equals(f1, f2, case=z3.BoolVal(True)):
    '''Check if two expressions are logically equivalent under the case.'''
    left2right = implies(f1, f2, case)
    right2left = implies(f2, f1, case)
    return left2right and right2left

def implies(f1, f2, case=z3.BoolVal(True)):
    '''Check if f1 implies f2 under the case.'''
    solver = z3.Solver()
    solver.add(case)
    return solver.check(f1, z3.Not(f2)) == z3.unsat

def is_valid(f):
    solver = z3.Solver()
    return solver.check(f) == z3.sat

def is_tautology(f):
    return equals(f, z3.BoolVal(True))

def is_contradiction(f):
    return equals(f, z3.BoolVal(False))

def is_literal(f):
    return is_atom(f) or z3.is_not(f) and is_atom(f.arg(0))

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

def is_atom(t):
    if not z3.is_bool(t):
        return False
    if not z3.is_app(t):
        return False
    k = t.decl().kind()
    if k == z3.Z3_OP_AND or k == z3.Z3_OP_OR or k == z3.Z3_OP_IMPLIES:
        return False
    if k == z3.Z3_OP_EQ and z3.is_bool(t.arg(0)):
        return False
    if k == z3.Z3_OP_TRUE or k == z3.Z3_OP_FALSE or k == z3.Z3_OP_XOR or k == z3.Z3_OP_NOT:
        return False
    return True

def atoms(fml):
    visited = set([])
    atms = set([])
    def atoms_rec(t, visited, atms):
        if t in visited:
            return
        visited |= { t }
        if is_atom(t):
            atms |= { t }
        for s in t.children():
            atoms_rec(s, visited, atms)
    atoms_rec(fml, visited, atms)
    return atms

def atom2literal(m, a):
    if z3.is_true(m.eval(a)):
        return a
    return z3.Not(a)

def implicant(atoms, s, snot):
    m = snot.model()
    lits = [atom2literal(m, a) for a in atoms]
    is_sat = s.check(lits)
    assert is_sat == z3.unsat
    core = s.unsat_core()
    return z3.Or([z3.mk_not(c) for c in core])

def to_cnf(fml):
    str(fml)
    atms = atoms(fml)
    s = z3.Solver()
    snot = z3.Solver()
    snot.add(z3.Not(fml))
    s.add(fml)

    while z3.sat == snot.check():
        clause = implicant(atms, s, snot)
        yield clause
        snot.add(clause)

def to_dnf(fml):
    not_fml = z3.Not(fml)
    cnf = list(to_cnf(not_fml))
    dnf = []
    for clause in cnf:
        literals = clause.children()
        dnf.append([z3.Not(lit) for lit in literals])
    return dnf

def atom2canonical(atom):
    '''Convert atom to a canonical form.'''
    if z3.is_lt(atom):
        return atom.arg(1) - atom.arg(0) - 1 >= 0
    elif z3.is_le(atom):
        return atom.arg(1) - atom.arg(0) >= 0
    elif z3.is_gt(atom):
        return atom.arg(0) - atom.arg(1) - 1 >= 0
    elif z3.is_ge(atom):
        return atom.arg(0) - atom.arg(1) >= 0
    elif z3.is_eq(atom):
        return atom.arg(0) - atom.arg(1) == 0

def literal2canonical(literal):
    '''Convert literal to a canonical form.'''
    if not z3.is_not(literal):
        return [atom2canonical(literal)]
    atom = literal.arg(0)
    if z3.is_lt(atom):
        return [atom2canonical(atom.arg(0) >= atom.arg(1))]
    elif z3.is_le(atom):
        return [atom2canonical(atom.arg(0) > atom.arg(1))]
    elif z3.is_gt(atom):
        return [atom2canonical(atom.arg(0) <= atom.arg(1))]
    elif z3.is_ge(atom):
        return [atom2canonical(atom.arg(0) < atom.arg(1))]
    elif z3.is_eq(atom):
        return [atom2canonical(atom.arg(0) > atom.arg(1)), atom2canonical(atom.arg(0) < atom.arg(1))]

def merge_cases(conditions, expressions):
    """
    Merge cases with equivalent expressions under their respective conditions.
    
    Args:
        conditions: List of Z3 boolean expressions (conditions)
        expressions: List of Z3 expressions (corresponding expressions)
    
    Returns:
        Tuple of (merged_conditions, merged_expressions)
    """
    import z3
    
    def conditionally_eq(cond, e1, e2):
        """Check if e1 and e2 are equivalent under the condition cond"""
        solver = z3.Solver()
        solver.set("timeout", 3000)  # 3 seconds timeout
        solver.add(cond)
        solver.add(e1 != e2)
        return solver.check() == z3.unsat
    
    pivot = 0
    res_conditions = conditions.copy()
    res_expressions = expressions.copy()
    
    while pivot < len(res_expressions):
        merged = set()
        pivot_expr = res_expressions[pivot]
        pivot_cond = res_conditions[pivot]
        
        # Iterate through to check if some case is equivalent to pivot expression
        for i in range(len(res_expressions)):
            if i == pivot:  # skip pivot
                continue
            if i in merged:  # skip already merged
                continue
            
            if conditionally_eq(res_conditions[i], pivot_expr, res_expressions[i]):
                pivot_cond = z3.Or(pivot_cond, res_conditions[i])
                merged.add(i)
        
        new_conditions = []
        new_expressions = []
        new_pivot_location = 0
        
        for i in range(len(res_conditions)):
            if i in merged:  # skip merged
                continue
            
            if i == pivot:
                new_pivot_location = len(new_conditions)
                new_conditions.append(pivot_cond)
            else:
                new_conditions.append(res_conditions[i])
            
            new_expressions.append(res_expressions[i])
        
        if merged:  # if we merged something
            pivot = new_pivot_location + 1
        else:
            pivot += 1
        
        res_conditions = new_conditions
        res_expressions = new_expressions
    
    return res_conditions, res_expressions

class DNFConverter:
    def __init__(self):
        pass

    def to_dnf(self, fml):
        return to_dnf(fml)

    # def to_dnf(self, f):
    #     nnf = z3.Or([z3.And(*c) for c in z3.Tactic('nnf').apply(f)])
    #     vars = get_vars(nnf)
    #     if any('!' in str(var) for var in vars):
    #         solver = z3.Solver()
    #         fresh_vars = [var for var in vars if str(var).startswith('z3name')]
    #         observers = {var: z3.Int('observer%d' % i) for i, var in enumerate(fresh_vars)}
    #         solver.add([observers[var] == var for var in fresh_vars])
    #         if solver.check(nnf) == z3.sat:
    #             m = solver.model()
    #             for var in fresh_vars:
    #                 m_var = m.eval(observers[var])
    #                 if solver.check(nnf, var != m_var) == z3.unsat:
    #                     nnf = z3.substitute(nnf, (var, m_var))
    #     temp_vars = [var for var in vars if '!' in str(var)]
    #     cons = {z3.IntSort(): z3.Int, z3.BoolSort(): z3.Bool, z3.RealSort(): z3.Real}
    #     name_mapping = [(var, cons[var.sort()](str(var).replace('!', '_'))) for var in temp_vars]
    #     nnf = z3.substitute(nnf, name_mapping)
    #     raw_dnf = self._to_dnf(nnf)
    #     return raw_dnf

    # def or2list(self, f):
    #     assert(z3.is_or(f) or z3.is_false(f) or z3.is_true(f))
    #     if z3.is_true(f) or z3.is_false(f):
    #         return [[f]]
    #     return [[c] for c in f.children()]

    # def _to_dnf(self, f):
    #     '''Convert f into dnf with early simplification'''
    #     if is_literal(f):
    #         return [[f]]
    #     args = [self._to_dnf(arg) for arg in f.children()]
    #     if z3.is_and(f):
    #         args_as_and = [self.disjunction2z3(arg) for arg in args if len(arg) != 0]
    #         simplified_list = [c for c in self.simplify_and(args_as_and)]
    #         simplified_args = [self.or2list(c) for c in simplified_list]
    #         new_disjunction = []
    #         for conjunctions in product(*simplified_args):
    #             new_disjunction.append(self.simplify_and(sum(conjunctions, [])))
    #         return new_disjunction
    #     return self.simplify_or(sum(args, []))

    # def disjunction2z3(self, disjunction):
    #     return z3.Or([z3.And(d) for d in disjunction])

    # def conjunction2z3(self, conjunction):
    #     return z3.And(conjunction)
    #         
    # def simplify_and(self, conjunction):
    #     removed = []
    #     if is_contradiction(self.conjunction2z3(conjunction)):
    #         return [z3.BoolVal(False)]

    #     for i, conjunct in enumerate(conjunction):
    #         rest_conjunctions = [c for j, c in enumerate(conjunction) if j != i and j not in removed]
    #         rest = self.conjunction2z3(rest_conjunctions)
    #         if implies(rest, conjunct):
    #             removed.append(i)
    #     res = [conjunct for i, conjunct in enumerate(conjunction) if i not in removed]
    #     assert(equals(self.conjunction2z3(res), self.conjunction2z3(conjunction)))
    #     return res
    
    # def simplify_or(self, disjunction):
    #     removed = []
    #     if is_tautology(self.disjunction2z3(disjunction)):
    #         return [[z3.BoolVal(True)]]

    #     for i, disjunct in enumerate(disjunction):
    #         rest_disjunction = [d for j, d in enumerate(disjunction) if j != i and j not in removed]
    #         rest = self.disjunction2z3(rest_disjunction)
    #         if implies(self.conjunction2z3(disjunct), rest):
    #             removed.append(i)
    #     res = [self.simplify_and(disjunct) for i, disjunct in enumerate(disjunction) if i not in removed]
    #     assert(equals(self.disjunction2z3(res), self.disjunction2z3(disjunction)))
    #     return res

def merge_conjunctions(conjunction):
    '''simplify conjunction by checking if some conjunct is implied by the rest.
       do it recursively until fix point.'''
    for i, conjunct in enumerate(conjunction):
        rest_conjunctions = [c for j, c in enumerate(conjunction) if j != i]
        rest = z3.And(rest_conjunctions)
        if implies(rest, conjunct):
            return merge_conjunctions(rest_conjunctions)
    return conjunction

def my_simplify(expr: z3.ExprRef, assumption: Optional[z3.ExprRef] = None) -> z3.ExprRef:
    """
    Simplify a Z3 expression by converting to CNF and removing entailed clauses.
    
    Args:
        expr: The Z3 expression to simplify
        assumption: Optional assumption to add to the solver
    
    Returns:
        Simplified Z3 expression
    """
    new_expr = simplify(expr)
    clauses = to_cnf(new_expr)
    solver = z3.Solver()
    
    if assumption is not None:
        solver.add(assumption)
    
    remains = []
    
    for clause in clauses:
        solver.push()
        solver.add(z3.Not(clause))
        if solver.check() == z3.sat:
            # This clause is not entailed, so keep it
            neg = [z3.Not(c) for c in clause.children()]
            simplified_neg = merge_conjunctions(neg)
            simplified_clause = z3.Or([z3.Not(lit) for lit in simplified_neg])
            remains.append(simplify(simplified_clause))
        solver.pop()
    
    return simplify(z3.And(remains)) if remains else expr.ctx().BoolVal(True)

def merge_cases(conditions, expressions):
    """
    Merge cases with equivalent expressions under their respective conditions.
    
    Args:
        conditions: List of Z3 boolean expressions (conditions)
        expressions: List of Z3 expressions (corresponding expressions)
    
    Returns:
        Tuple of (merged_conditions, merged_expressions)
    """
    import z3
    
    def conditionally_eq(cond, e1, e2):
        """Check if e1 and e2 are equivalent under the condition cond"""
        solver = z3.Solver()
        solver.set("timeout", 3000)  # 3 seconds timeout
        solver.add(cond)
        solver.add(e1 != e2)
        return solver.check() == z3.unsat
    
    pivot = 0
    res_conditions = conditions.copy()
    res_expressions = expressions.copy()
    
    while pivot < len(res_expressions):
        merged = set()
        pivot_expr = res_expressions[pivot]
        pivot_cond = res_conditions[pivot]
        
        # Iterate through to check if some case is equivalent to pivot expression
        for i in range(len(res_expressions)):
            if i == pivot:  # skip pivot
                continue
            if i in merged:  # skip already merged
                continue
            
            if conditionally_eq(res_conditions[i], pivot_expr, res_expressions[i]):
                pivot_cond = z3.Or(pivot_cond, res_conditions[i])
                merged.add(i)
        
        new_conditions = []
        new_expressions = []
        new_pivot_location = 0
        
        for i in range(len(res_conditions)):
            if i in merged:  # skip merged
                continue
            
            if i == pivot:
                new_pivot_location = len(new_conditions)
                new_conditions.append(my_simplify(pivot_cond))
            else:
                new_conditions.append(my_simplify(res_conditions[i]))
            
            new_expressions.append(res_expressions[i])
        
        if merged:  # if we merged something
            pivot = new_pivot_location + 1
        else:
            pivot += 1
        
        res_conditions = new_conditions
        res_expressions = new_expressions
    
    return res_conditions, res_expressions

x = Int('x')
conditions = [x > 0, x < 10, x == 5, x == -1]
expressions = [x + 1, x + 2, 6, 0]

merged_conditions, merged_expressions = merge_cases(conditions, expressions)
print("Merged Conditions:", merged_conditions)
print("Merged Expressions:", merged_expressions)