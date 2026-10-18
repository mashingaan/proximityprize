"""Exact tests of the candidate affine-syndrome locator invariant.

Finite tests only. This is not a production threshold certificate.
"""
from itertools import product
import json
import sympy as sp


def exhaustive_rank_two():
    p = 3

    def trim(a):
        a = [x % p for x in a]
        while len(a) > 1 and a[-1] == 0:
            a.pop()
        return tuple(a)

    def add(a, b):
        c = [0] * max(len(a), len(b))
        for i, x in enumerate(a):
            c[i] += x
        for i, x in enumerate(b):
            c[i] += x
        return trim(c)

    def mul(a, b):
        c = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                c[i + j] += x * y
        return trim(c)

    def sub(a, b):
        return add(a, tuple(-x for x in b))

    def divmod_poly(a, b):
        assert b != (0,)
        q = [0] * max(1, len(a) - len(b) + 1)
        while a != (0,) and len(a) >= len(b):
            k = len(a) - len(b)
            c = a[-1] * pow(b[-1], -1, p) % p
            q[k] = c
            a = sub(a, (0,) * k + tuple(c * x for x in b))
        return trim(q), a

    def gcd(a, b):
        while b != (0,):
            a, b = b, divmod_poly(a, b)[1]
        if a == (0,):
            return a
        return trim([x * pow(a[-1], -1, p) for x in a])

    counts = dict(pencils=0, singular=0, rank_two=0, moving=0, stationary=0)
    for coeff in product(range(p), repeat=10):
        counts['pencils'] += 1
        a, b, c, d, e = [trim(coeff[2*i:2*i+2]) for i in range(5)]
        v = [sub(mul(b, d), mul(c, c)), sub(mul(b, c), mul(a, d)),
             sub(mul(a, c), mul(b, b))]
        det = add(add(mul(c, v[0]), mul(d, v[1])), mul(e, v[2]))
        if det != (0,):
            continue
        counts['singular'] += 1
        if v[2] == (0,):
            continue
        counts['rank_two'] += 1
        common = gcd(gcd(v[0], v[1]), v[2])
        primitive = []
        for entry in v:
            quotient, remainder = divmod_poly(entry, common)
            assert remainder == (0,)
            primitive.append(quotient)
        degree = max(len(x) - 1 for x in primitive)
        h = 0
        for x in range(p):
            value = (0,)
            for i, entry in enumerate(primitive):
                value = add(value, tuple(x**i * c for c in entry))
            h += int(value == (0,))
        assert 2 * degree <= 2 - h, (coeff, primitive, h)
        counts['moving'] += int(degree > 0)
        counts['stationary'] += h
    assert counts == dict(pencils=59049, singular=1377, rank_two=1080,
                          moving=432, stationary=600)
    return counts


def structured_case(p, moving_degree, fixed_nodes):
    z, x = sp.symbols('z x')
    rho = moving_degree + len(fixed_nodes)
    assert 2 * rho < 3 * moving_degree - 1
    assert (p - 1) % moving_degree == 0

    def mod(expr):
        return sp.Poly(sp.expand(expr), z, modulus=p).as_expr()

    # Weights cancel the moving contribution at the first fixed node
    # when that node belongs to the moving root set.
    weights = [(-pow(moving_degree * pow(a, moving_degree - 1, p), -1, p)) % p
               for a in fixed_nodes]
    s = []
    for j in range(2 * rho + 1):
        moving = 1 if j == moving_degree - 1 else z if j == 2 * moving_degree - 1 else 0
        s.append(mod(moving + sum(w * a**j for a, w in zip(fixed_nodes, weights))))
    g = sp.Poly(sp.prod(x-a for a in fixed_nodes), x, modulus=p)
    locator = sp.Poly(sp.expand(g.as_expr() * (x**moving_degree-z)), x)
    v = [mod(locator.nth(i)) for i in range(rho+1)]
    hmat = sp.Matrix(rho+1, rho+1, lambda i, j: s[i+j])
    assert all(mod(y) == 0 for y in hmat * sp.Matrix(v))
    delta = mod(hmat[:rho, :rho].det(method='domain-ge'))
    assert delta != 0
    # Independent cofactors, including the highest-z-degree component.
    i = max(range(rho+1), key=lambda j: sp.degree(v[j], z))
    cofactor = mod(hmat.minor_submatrix(i, i).det(method='domain-ge'))
    assert mod(cofactor - delta*v[i]**2) == 0
    assert sp.degree(cofactor, z) <= rho

    filtered = [mod(sum(int(g.nth(a))*s[j+a] for a in range(g.degree()+1)))
                for j in range(2*moving_degree+1)]
    filtered_h = sp.Matrix(moving_degree+1, moving_degree+1,
                           lambda i, j: filtered[i+j])
    reduced_v = sp.Matrix([-z] + [0]*(moving_degree-1) + [1])
    assert all(mod(y) == 0 for y in filtered_h * reduced_v)
    filtered_delta = mod(filtered_h[:moving_degree, :moving_degree].det(method='domain-ge'))
    assert filtered_delta != 0
    filtered_cofactor = mod(filtered_h.minor_submatrix(0, 0).det(method='domain-ge'))
    assert mod(filtered_cofactor-filtered_delta*z**2) == 0
    assert sp.degree(filtered_cofactor, z) <= moving_degree

    good, rank_drops, cancellations = [], [], []
    for parameter in range(p):
        roots = [a for a in range(1, p) if pow(a, moving_degree, p) == parameter]
        if len(roots) != moving_degree:
            continue
        errors = {a: pow(moving_degree*pow(a, moving_degree-1, p), -1, p) for a in roots}
        for a, w in zip(fixed_nodes, weights):
            errors[a] = (errors.get(a, 0) + w) % p
        if any(w == 0 for w in errors.values()):
            cancellations.append(parameter)
        errors = {a: w for a, w in errors.items() if w}
        for j in range(2*rho+1):
            observed = sum(w*pow(a, j, p) for a, w in errors.items()) % p
            assert observed == int(s[j].subs(z, parameter)) % p
        assert all(int(sp.expand(locator.as_expr()).subs({z:parameter, x:a})) % p == 0
                   for a in errors)
        assert len(errors) <= rho
        if len(errors) < rho:
            rank_drops.append(parameter)
            assert int(sp.sympify(delta).subs(z, parameter)) % p == 0
        good.append(parameter)
    assert good
    if fixed_nodes:
        assert rank_drops and cancellations
    return dict(field=p, rank=rho, moving_degree=moving_degree,
                fixed_nodes=fixed_nodes, good_parameters=good,
                rank_drop_parameters=rank_drops, cancellation_parameters=cancellations,
                determinant_degree=int(sp.degree(delta, z)),
                filtered_cofactor_degree=int(sp.degree(filtered_cofactor, z)))


if __name__ == '__main__':
    report = dict(exhaustive_rank_two=exhaustive_rank_two(),
                  structured=[structured_case(7, 3, []),
                              structured_case(17, 4, [1]),
                              structured_case(19, 6, [1, 2])],
                  production_threshold_proved=False)
    print(json.dumps(report, indent=2))
