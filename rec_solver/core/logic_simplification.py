'''This module contains the logic simplification functions.'''

import z3
from itertools import product

def equals(f1, f2):
    '''Check if two expressions are logically equivalent.'''
    left2right = implies(f1, f2)
    right2left = implies(f2, f1)
    return left2right and right2left

def implies(f1, f2):
    '''Check if f1 implies f2.'''
    solver = z3.Solver()
    return solver.check(f1, z3.Not(f2)) == z3.unsat

def is_valid(f):
    solver = z3.Solver()
    return solver.check(f) == z3.sat

def is_tautology(f):
    return equals(f, z3.BoolVal(True))

def is_contradiction(f):
    return equals(f, z3.BoolVal(False))

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

def is_literal(f):
    return is_atom(f) or z3.is_not(f) and is_atom(f.arg(0))

class DNFConverter:
    def __init__(self):
        pass

    def to_dnf(self, f):
        nnf = z3.Or([z3.And(*c) for c in z3.Tactic('nnf').apply(f)])
        raw_dnf = self._to_dnf(nnf)
        return raw_dnf

    def or2list(self, f):
        assert(z3.is_or(f) or z3.is_false(f) or z3.is_true(f))
        if z3.is_true(f) or z3.is_false(f):
            return [[f]]
        return [[c] for c in f.children()]

    def _to_dnf(self, f):
        '''Convert f into dnf with early simplification'''
        if is_literal(f):
            return [[f]]
        args = [self._to_dnf(arg) for arg in f.children()]
        if z3.is_and(f):
            args_as_and = [self.disjunction2z3(arg) for arg in args if len(arg) != 0]
            simplified_list = [c for c in self.simplify_and(args_as_and)]
            simplified_args = [self.or2list(c) for c in simplified_list]
            new_disjunction = []
            for conjunctions in product(*simplified_args):
                new_disjunction.append(self.simplify_and(sum(conjunctions, [])))
            return new_disjunction
        return self.simplify_or(sum(args, []))

    def disjunction2z3(self, disjunction):
        return z3.Or([z3.And(d) for d in disjunction])

    def conjunction2z3(self, conjunction):
        return z3.And(conjunction)
            
    def simplify_and(self, conjunction):
        removed = []
        if is_contradiction(self.conjunction2z3(conjunction)):
            return [z3.BoolVal(False)]

        for i, conjunct in enumerate(conjunction):
            rest_conjunctions = [c for j, c in enumerate(conjunction) if j != i and j not in removed]
            rest = self.conjunction2z3(rest_conjunctions)
            if implies(rest, conjunct):
                removed.append(i)
        res = [conjunct for i, conjunct in enumerate(conjunction) if i not in removed]
        assert(equals(self.conjunction2z3(res), self.conjunction2z3(conjunction)))
        return res
    
    def simplify_or(self, disjunction):
        removed = []
        if is_tautology(self.disjunction2z3(disjunction)):
            return [[z3.BoolVal(True)]]

        for i, disjunct in enumerate(disjunction):
            rest_disjunction = [d for j, d in enumerate(disjunction) if j != i and j not in removed]
            rest = self.disjunction2z3(rest_disjunction)
            if implies(self.conjunction2z3(disjunct), rest):
                removed.append(i)
        res = [self.simplify_and(disjunct) for i, disjunct in enumerate(disjunction) if i not in removed]
        assert(equals(self.disjunction2z3(res), self.disjunction2z3(disjunction)))
        return res

if __name__ == '__main__':
    from z3 import *
    c, z = Ints('c z')
    q0, q1, q2 = Ints('q0 q1 q2')
    conjunction = [c >= 1, c >= 0, z >= 3, z <= 4, z + c >= 4]
    disjunction = [[c >= 1, c >= 0], [c <= 2]]
    converter = DNFConverter()
    testing = z3.And(c + z >= 1, c + z <= 1, z3.Or(c >= 0, z <= 0), c >= -20)
    # print(converter.simplify_and(conjunction))
    # print(converter.simplify_or(disjunction))
    simplified = z3.simplify(converter.disjunction2z3(converter.to_dnf(testing)))
    print(simplified)
    print(equals(testing, simplified))
    # print(converter.to_dnf(z3.Or([z3.And(d) for d in disjunction])))
    cond = And(q0 >= 1,
        q1 >= 1,
        q2 >= 1,
        0 >= -1*q2 + -1*q1 + -1*q0 + z,
        Not(And(-1*z + c <= -1,
                Or(Not(q0 >= 1),
                   Not(q1 >= 1),
                   Not(q2 >= 1),
                   -1*q0 + z + -1*c <= 0,
                   And(q1 + q0 + -1*z + c <= -1,
                       -1*q2 + -1*q1 + -1*q0 + z + -1*c <= 0),
                   And(q0 + -1*z + c <= -1,
                       -1*q1 + -1*q0 + z + -1*c <= 0,
                       c <= -1),
                   And(q2 + q1 + q0 + -1*z + c <= -1,
                       Not(0 >= -1*q2 + -1*q1 + -1*q0 + z))))),
        Not(And(-1*z + c <= -2,
                Or(Not(q0 >= 1),
                   Not(q1 >= 1),
                   Not(q2 >= 1),
                   And(-1*q0 + z + -1*c <= 1, c <= -2),
                   And(q0 + -1*z + c <= -2,
                       -1*q1 + -1*q0 + z + -1*c <= 1),
                   And(q1 + q0 + -1*z + c <= -2,
                       -1*q2 + -1*q1 + -1*q0 + z + -1*c <= 1,
                       c <= -2),
                   And(q2 + q1 + q0 + -1*z + c <= -2,
                       Not(0 >= -1*q2 + -1*q1 + -1*q0 + z))))),
        Not(And(-1*q2 + -1*q1 + -1*q0 <= -1,
                Or(Not(q0 >= 1),
                   Not(q1 >= 1),
                   Not(q2 >= 1),
                   And(-1*q2 + -1*q1 <= -1,
                       q2 <= 0,
                       Or(-1*z + c + q2 + q1 + q0 <= -2,
                          z + -1*c + -1*q2 + -1*q1 + -1*q0 <= -1,
                          z + -1*q2 + -1*q1 + -1*q0 <= -1)),
                   And(q2 + q1 <= 0,
                       Or(z + -1*q2 + -1*q1 + -1*q0 <= -1,
                          And(-1*z + c + q2 + q1 + q0 <= -1,
                              -1*c + z + -1*q2 + -1*q1 + -1*q0 <=
                              0))),
                   And(q2 >= 1,
                       Or(z + -1*q2 + -1*q1 + -1*q0 <= -1,
                          And(-1*z + c + q2 + q1 + q0 <= -1,
                              -1*c + z + -1*q2 + -1*q1 + -1*q0 <=
                              0)))))),
        Not(And(q0 >= 1,
                Or(Not(q0 >= 1),
                   Not(q1 >= 1),
                   z + -1*q0 <= -1,
                   Not(q2 >= 1),
                   And(q1 <= -1,
                       -1*q2 + -1*q1 <= -1,
                       Or(z + -1*q0 <= -1,
                          And(-1*z + c + q0 <= -1,
                              -1*c + z + -1*q0 <= 0))),
                   And(q2 + q1 <= -1,
                       Not(0 >= -1*q2 + -1*q1 + -1*q0 + z)),
                   And(-1*z + c + q0 <= -1,
                       -1*c + z + -1*q0 <= 0)))),
        Not(And(-1*q1 + -1*q0 <= -1,
                Or(Not(q0 >= 1),
                   Not(q1 >= 1),
                   Not(q2 >= 1),
                   And(q2 <= -1,
                       Not(0 >= -1*q2 + -1*q1 + -1*q0 + z)),
                   And(q1 >= 1,
                       Or(z + -1*q1 + -1*q0 <= -1,
                          z + -1*c + -1*q1 + -1*q0 <= -1,
                          -1*z + c + q1 + q0 <= -2)),
                   And(q1 <= -1,
                       Or(z + -1*q1 + -1*q0 <= -1,
                          And(-1*z + c + q1 + q0 <= -1,
                              -1*c + z + -1*q1 + -1*q0 <= 0)))))))
    # cond = And(q0 >= 1,
    # Not(And(Not(0 >= -1*q0 + z), Not(c == -1 + -1*q0 + z))),
    # Not(And(q0 >= 1,
    #         Or(Not(q0 >= 1),
    #            z + -1*q0 <= -1,
    #            And(-1*z + c + q0 <= -1,
    #                -1*c + z + -1*q0 <= 0)))),
    # Not(And(-1*z + c <= -1,
    #         Or(Not(q0 >= 1),
    #            And(Not(0 >= -1*q0 + z),
    #                q0 + -1*z + c <= -1,
    #                Not(c == -1 + -1*q0 + z)),
    #            -1*q0 + z + -1*c <= 0))))
    nnf_cond = z3.Or([z3.And(*c) for c in z3.Tactic('nnf').apply(cond)])
    simplified = z3.simplify(converter.disjunction2z3(converter.to_dnf(nnf_cond))) 
    print(simplified)
    print(equals(cond, simplified))