import sympy as sp
from itertools import product
from ..recurrence import Recurrence

def gen_poly_template(X, d):
    monomials = {sp.Integer(1)}
    for _ in range(d):
        monomials_pair = set(product(X, monomials))
        monomials = monomials.union(set(x*y for x, y in monomials_pair))
    monomials = list(monomials)
    coeffs = sp.symbols('a:%d' % len(monomials), Real=True)
    res = sum([a*m for a, m in zip(coeffs, monomials)])
    return res.as_poly(*X), list(coeffs), monomials

def vec_space_d(X, transitions, ind_var, d):
    poly_template, coeffs, monomials = gen_poly_template(X, d)
    possible_k = None
    for tran in transitions:
        next_poly = poly_template.as_expr().subs({ind_var: ind_var + 1}, simultaneous=True)
        poly_prime = next_poly.as_expr().subs(tran, simultaneous=True).as_poly(*X)
        coords = [mono.as_expr().subs({ind_var: ind_var + 1}, simultaneous=True).subs(tran, simultaneous=True).as_poly(*X) for mono in monomials]
        ee = [mono.subs({ind_var: ind_var + 1}, simultaneous=True) for mono in monomials]
        M = sp.Matrix([[coord.coeff_monomial(mono) for mono in monomials] for coord in coords]).T
        # print(M.eigenvects())
        if possible_k is None:
            possible_k = set(M.eigenvals().keys())
        else:
            possible_k = possible_k.intersection(M.eigenvals().keys())

    ret = []
    for k in possible_k:
        all_coeffs = []
        for tran in transitions:
            next_poly = poly_template.as_expr().subs({ind_var: ind_var + 1}, simultaneous=True)
            poly_prime = next_poly.as_expr().subs(tran, simultaneous=True).as_poly(*X)
            # poly_coeffs = poly_prime.coeffs()
            rem = poly_prime - k*poly_template
            rem_coeffs = rem.coeffs()
            all_coeffs.extend(rem_coeffs)
        # const_dummy_symbol = sp.Symbol('aaaaa0', real=True)
        # coeffs.append(const_dummy_symbol)
        # for tran in transitions:
        #     next_poly = poly_template.as_expr().subs({ind_var: ind_var + 1}, simultaneous=True)
        #     poly_prime = next_poly.as_expr().subs(tran, simultaneous=True).as_poly(*X)
        #     rem = poly_prime - poly_template - const_dummy_symbol
        #     rem_coeffs = rem.coeffs()
        #     all_coeffs.extend(rem_coeffs)
        res, _ = sp.linear_eq_to_matrix(all_coeffs, *coeffs)
        basis = res.nullspace()
        basis_instances = []
        for vec in basis:
            instance = poly_template.subs({c: v for v, c in zip(vec, coeffs)}, simultaneous=True)
            basis_instances.append(instance)
        # symbolic_baiss = [(vec.T * Matrix(coeffs))[0] for vec in basis]
        ret.append((k, basis_instances))
        all_coeffs = []
    all_coeffs = []
    const_dummy_symbol = sp.Symbol('aaaaa0', real=True)
    coeffs.append(const_dummy_symbol)
    for tran in transitions:
        next_poly = poly_template.as_expr().subs({ind_var: ind_var + 1}, simultaneous=True)
        poly_prime = next_poly.as_expr().subs(tran, simultaneous=True).as_poly(*X)
        rem = poly_prime - poly_template - const_dummy_symbol
        rem_coeffs = rem.coeffs()
        all_coeffs.extend(rem_coeffs)
    res, _ = sp.linear_eq_to_matrix(all_coeffs, *coeffs)
    basis = res.nullspace()
    basis_instances = []
    for vec in basis:
        instance = poly_template.subs({c: v for v, c in zip(vec, coeffs)}, simultaneous=True)
        numerator, _ = sp.fraction(sp.factor(instance))
        basis_instances.append(numerator)
    if len(basis) != 0:
        ret.append((sp.Integer(1), basis_instances))
    return ret

def solve_rec(k, p, transitions, inits, ind_var):
    if k != 1:
        if k == 0:
            if sp.simplify(p.subs(inits, simultaneous=True) == 0):
                return (p, 0)
            else:
                return (p, sp.Piecewise((0, ind_var >= 1), (p.subs(inits, simultaneous=True), True)))
    else:
        cs = [sp.simplify(p.subs({ind_var: ind_var + 1}, simultaneous=True).subs(tran, simultaneous=True) - p) for tran in transitions]
        if all([c == cs[0] for c in cs]):
            c = cs[0]
            return (p, sp.simplify(p.subs(inits, simultaneous=True)) + ind_var*c)

def poly_expr_solving(rec: Recurrence, degr=2):
    # X = [func.subs({rec.ind_var: rec.ind_var - 1}) for func in rec.all_funcs]
    transitions = rec.transitions
    ks_instances = vec_space_d(rec.all_funcs, transitions, rec.ind_var, degr)
    for k, instances in ks_instances:
        for p in instances:
            print(solve_rec(k, p, transitions, rec.initial, rec.ind_var))
