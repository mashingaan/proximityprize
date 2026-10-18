"""Search a fixed small RS instance for a multidimensional-locator obstruction.

All arithmetic is in F_11. A found witness is independently checked using
polynomial interpolation on the actual agreement sets.
"""
from itertools import combinations, product
import json
import random

P, N, K, T = 11, 10, 5, 3
DOMAIN = list(range(1, P))
R = N-K


def syndrome(word):
    return tuple(sum(-x * word[i] * pow(x, j, P)
                     for i, x in enumerate(DOMAIN)) % P for j in range(R))


def key(values):
    result = 0
    for value in values:
        result = result*P+value
    return result


def interpolated_value(nodes, values, x):
    total = 0
    for i, a in enumerate(nodes):
        numerator, denominator = 1, 1
        for j, b in enumerate(nodes):
            if i != j:
                numerator = numerator*(x-b) % P
                denominator = denominator*(a-b) % P
        total += values[i]*numerator*pow(denominator, -1, P)
    return total % P


def extends_to_code(word, agreement):
    assert len(agreement) >= K
    chosen = agreement[:K]
    nodes = [DOMAIN[i] for i in chosen]
    values = [word[i] for i in chosen]
    return all(interpolated_value(nodes, values, DOMAIN[i]) == word[i]
               for i in agreement)


def main():
    columns = [tuple(-x*pow(x, j, P) % P for j in range(R)) for x in DOMAIN]
    lookup = {0: ()}
    patterns = 1
    for weight in range(1, T+1):
        for support in combinations(range(N), weight):
            for amplitudes in product(range(1, P), repeat=weight):
                values = tuple(sum(a*columns[i][j] for i, a in zip(support, amplitudes)) % P
                               for j in range(R))
                lookup.setdefault(key(values), tuple(zip(support, amplitudes)))
                patterns += 1
    assert patterns == 124601
    rng = random.Random(164239)
    attempts = 50000
    for trial in range(attempts):
        u0 = [rng.randrange(P) for _ in DOMAIN]
        u1 = [rng.randrange(P) for _ in DOMAIN]
        a, b = syndrome(u0), syndrome(u1)
        if all(x == 0 for x in b):
            continue
        error_patterns = []
        for z in range(P):
            pattern = lookup.get(key(tuple((x+z*y) % P for x, y in zip(a, b))))
            if pattern is None:
                break
            error_patterns.append(pattern)
        if len(error_patterns) != P:
            continue
        witnesses = []
        for z, pattern in enumerate(error_patterns):
            error = [0]*N
            for i, value in pattern:
                error[i] = value
            received = [(x+z*y) % P for x, y in zip(u0, u1)]
            head = [(x-e) % P for x, e in zip(received, error)]
            agreement = [i for i in range(N) if error[i] == 0]
            assert syndrome(head) == (0,)*R
            assert extends_to_code(head, list(range(N)))
            assert len(agreement) >= N-T
            if extends_to_code(u0, agreement) and extends_to_code(u1, agreement):
                break
            witnesses.append(dict(parameter=z, head=head,
                                  agreement_nodes=[DOMAIN[i] for i in agreement]))
        if len(witnesses) == P:
            return dict(field=P, n=N, k=K, t=T, exhaustive_error_patterns=patterns,
                        represented_syndromes=len(lookup), trial=trial,
                        result='FOUND_AND_INTERPOLATION_VERIFIED',
                        u0=u0, u1=u1, witnesses=witnesses,
                        locator_kernel_dimension_lower_bound=2*T+1-R,
                        sponsor_counterexample=False)
    return dict(field=P, n=N, k=K, t=T, exhaustive_error_patterns=patterns,
                represented_syndromes=len(lookup), attempts=attempts,
                result='NO_WITNESS_FOUND_IN_SEARCH',
                absence_proved=False, sponsor_counterexample=False)


if __name__ == '__main__':
    print(json.dumps(main(), indent=2))
