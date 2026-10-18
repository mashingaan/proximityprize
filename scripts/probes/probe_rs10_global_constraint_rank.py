"""Exact rank audit of the fixed RS10 witness incidence pattern.

The node labels and scalar parameters are fixed integers. This does not rule
out other patterns or varying parameters in other characteristics.
"""
from fractions import Fraction
from functools import reduce
from math import gcd, lcm
from pathlib import Path
import json
import sympy as sp
from sympy.matrices.normalforms import smith_normal_form


def modular_rank(rows, p):
    a = [[x % p for x in row] for row in rows]
    rank = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(rank, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][j], -1, p)
        a[rank] = [x*inv % p for x in a[rank]]
        for i in range(len(a)):
            if i != rank and a[i][j]:
                scale = a[i][j]
                a[i] = [(x-scale*y) % p for x, y in zip(a[i], a[rank])]
        rank += 1
    return rank


def bareiss_determinant(rows):
    a = [list(row) for row in rows]
    sign, previous = 1, 1
    for k in range(len(a)-1):
        pivot = next((i for i in range(k, len(a)) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        value = a[k][k]
        for i in range(k+1, len(a)):
            for j in range(k+1, len(a)):
                numerator = a[i][j]*value-a[i][k]*a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator//previous
            a[i][k] = 0
        previous = value
    return sign*a[-1][-1]


def main():
    fixture = json.loads((Path(__file__).parent/'fixtures'/'locator-rs10-f11.json')
                        .read_text(encoding='utf-8-sig'))
    rows, labels = [], []
    for witness in fixture['witnesses']:
        z = witness['parameter']
        nodes = witness['agreement_nodes']
        base = nodes[:5]
        for extra in nodes[5:]:
            six = base+[extra]
            rational = []
            for x in six:
                denominator = 1
                for y in six:
                    if y != x:
                        denominator *= x-y
                rational.append(Fraction(1, denominator))
            common = lcm(*(v.denominator for v in rational))
            weights = [int(v*common) for v in rational]
            content = reduce(gcd, (abs(v) for v in weights))
            weights = [v//content for v in weights]
            assert all(sum(w*x**j for x, w in zip(six, weights)) == 0 for j in range(5))
            row = [0]*10
            for x, w in zip(six, weights):
                if x >= 6:
                    row[x-6] += w
                    row[5+x-6] += z*w
            rows.append(row)
            labels.append(dict(parameter=z, nodes=six, weights=weights))
    matrix = sp.Matrix(rows)
    pivots = list(matrix.T.rref()[1])
    rank_q = len(pivots)
    assert rank_q == 10
    minor_rows = [rows[i] for i in pivots]
    determinant = bareiss_determinant(minor_rows)
    assert determinant == int(sp.Matrix(minor_rows).det()) != 0
    diagonal = smith_normal_form(matrix, domain=sp.ZZ)
    invariants = [abs(int(diagonal[i, i])) for i in range(10)]
    assert all(invariants)
    assert abs(determinant) % reduce(lambda x, y: x*y, invariants, 1) == 0
    rank11 = modular_rank(rows, 11)
    assert rank11 < rank_q
    print(json.dumps(dict(result='EXACT_FIXED_PATTERN_RANK_DROP',
                          matrix_shape=[len(rows), 10], rational_rank=rank_q,
                          rank_mod_11=rank11, pivot_row_indices=pivots,
                          full_rank_minor=minor_rows, minor_determinant=determinant,
                          smith_invariants_diagnostic=invariants,
                          row_certificates=labels,
                          scope='fixed integer nodes and parameters only',
                          sponsor_bound_proved=False), indent=2))


if __name__ == '__main__':
    main()
