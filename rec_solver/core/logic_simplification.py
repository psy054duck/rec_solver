'''This module contains the logic simplification functions.'''

import z3
from itertools import combinations

def equals(f1, f2):
    '''Check if two expressions are logically equivalent.'''
    return implies(f1, f2) and implies(f2, f1)

def implies(f1, f2):
    '''Check if f1 implies f2.'''
    solver = z3.Solver()
    return solver.check(f1, z3.Not(f2)) == z3.unsat

############################ This part is for factorization ####################
def factorize(f, hints=None):
    '''Factorize the expression f.'''
    assert(hints is not None)
    return _factorize(f, hints)
    
def _factorize(f, factors):
    '''Factorize the expression f by the factor.
       It returns a tuple (factors, remain) where factors is a list of atoms, remain is the remaining expression
       ensuring that f <=> prod(factors) ^ remain.
       It aims to simplify the input formula in the sense that "remain" contains less atoms.'''
    pass

def factorize_atom(atom, factors):
    '''Check if atom is equivalent to factors,
       if so, return an empty list.'''
    if equals(atom, z3.And(factors)):
        return []

def factorize_and(f, factors):
    '''Check if any combination of conjuncts in f is equivalent to factors,
       if so, return the remaining conjuncts.'''
    possible_conjuncts = []
    for conjunct in f.children():
        if implies(z3.And(factors), conjunct):
            possible_conjuncts.append(conjunct)
    eq_conjuncts = None
    for cnt in range(1, len(possible_conjuncts) + 1):
        for conjuncts in combinations(possible_conjuncts, cnt):
            if implies(z3.And(conjuncts), z3.And(factors)):
                eq_conjuncts = conjuncts
                break
        if eq_conjuncts is not None:
            break
    return z3.And([conjunct for conjunct in f.children() if conjunct not in eq_conjuncts])

# def factorize_or(f, factors):
#     if all(_factorize)
################################################################################ 
