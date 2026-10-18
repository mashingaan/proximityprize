"""Independent polynomial and dual-functional verification of the RS[10,5] fixture.

No syndrome decoder or random search is used. The modular identities are also
valid under the embedding of F_11 into any field of characteristic eleven.
"""
from itertools import combinations
from pathlib import Path
import json

P = 11


def multiply(a, b):
    c = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] = (c[i+j]+x*y) % P
    return c


def interpolate(nodes, values):
    result = [0]*len(nodes)
    for i, x in enumerate(nodes):
        basis, denominator = [1], 1
        for j, y in enumerate(nodes):
            if i != j:
                basis = multiply(basis, [-y, 1])
                denominator = denominator*(x-y) % P
        scale = values[i]*pow(denominator, -1, P) % P
        for j, coefficient in enumerate(basis):
            result[j] = (result[j]+scale*coefficient) % P
    return result


def main():
    path = Path(__file__).parent/'fixtures'/'locator-rs10-f11.json'
    fixture = json.loads(path.read_text(encoding='utf-8-sig'))
    assert (fixture['field'], fixture['n'], fixture['k'], fixture['t']) == (11, 10, 5, 3)
    u0, u1 = fixture['u0'], fixture['u1']
    assert len(u0) == len(u1) == 10
    assert all(type(x) is int and 0 <= x < P for x in u0+u1)
    assert sorted(w['parameter'] for w in fixture['witnesses']) == list(range(P))
    records = []
    locator_ranks = []
    for witness in fixture['witnesses']:
        z = witness['parameter']
        received = [(a+z*b) % P for a, b in zip(u0, u1)]
        moments = [sum(-x*received[x-1]*pow(x, j, P) for x in range(1, P)) % P
                   for j in range(5)]
        rows = [moments[:4], moments[1:]]
        rank_two = any((rows[0][i]*rows[1][j]-rows[0][j]*rows[1][i]) % P
                       for i, j in combinations(range(4), 2))
        locator_ranks.append(2 if rank_two else int(any(moments)))
        head = witness['head']
        assert len(head) == 10
        assert all(type(x) is int and 0 <= x < P for x in head)
        coeff = interpolate(list(range(1, 6)), head[:5])
        assert all(sum(c*pow(x, j, P) for j, c in enumerate(coeff)) % P == head[x-1]
                   for x in range(1, P))
        agreement = witness['agreement_nodes']
        assert len(set(agreement)) == len(agreement) >= 7
        assert all(type(x) is int and 1 <= x < P for x in agreement)
        assert all((u0[x-1]+z*u1[x-1]-head[x-1]) % P == 0 for x in agreement)
        dual = None
        for nodes in combinations(agreement, 6):
            weights = []
            for x in nodes:
                denominator = 1
                for y in nodes:
                    if y != x:
                        denominator = denominator*(x-y) % P
                weights.append(pow(denominator, -1, P))
            assert all(sum(w*pow(x, j, P) for x, w in zip(nodes, weights)) % P == 0
                       for j in range(5))
            for row_index, row in enumerate([u0, u1]):
                value = sum(w*row[x-1] for x, w in zip(nodes, weights)) % P
                if value:
                    dual = dict(nodes=list(nodes), weights=weights,
                                rejected_row=row_index, nonzero_value=value)
                    break
            if dual is not None:
                break
        assert dual is not None
        records.append(dict(parameter=z, code_coefficients=coeff,
                            agreement_nodes=agreement, annihilator=dual))
    print(json.dumps(dict(result='EXACT_POLYNOMIAL_AND_DUAL_CERTIFICATE_PASS',
                          field_characteristic=P, n=10, k=5, t=3,
                          bad_parameter_count=len(records), u0=u0, u1=u1,
                          locator_matrix_ranks=locator_ranks,
                          records=records, lean_verified=False,
                          sponsor_counterexample=False), indent=2))


if __name__ == '__main__':
    main()
