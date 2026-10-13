"""Exhaustive finite-field abstract-code census, not a sponsor-scale certificate."""
import itertools
import json


def census(p, n, t):
    """One-dimensional full-support code, normalized to the repetition code."""
    words = list(itertools.product(range(p), repeat=n))
    histogram = {}
    best = -1
    example = None
    for u0 in words:
        for u1 in words:
            bad = []
            for gamma in range(p):
                received = tuple((a+gamma*b) % p for a,b in zip(u0,u1))
                witnesses = []
                for head in range(p):
                    agreement = tuple(i for i,y in enumerate(received) if y == head)
                    for support in itertools.combinations(agreement, n-t):
                        joint = (len({u0[i] for i in support}) == 1
                                 and len({u1[i] for i in support}) == 1)
                        if not joint:
                            witnesses.append(dict(head=head, agreement=list(support),
                                                  errors=[i for i in range(n)
                                                          if i not in support]))
                if witnesses:
                    bad.append(dict(gamma=gamma,witnesses=witnesses))
            size = len(bad)
            histogram[size] = histogram.get(size,0)+1
            if size > best:
                best = size
                example = dict(u0=list(u0),u1=list(u1),bad=bad)
    assert sum(histogram.values()) == p**(2*n)
    return dict(field=p,length=n,dimension=1,error_budget=t,
                stacks_checked=p**(2*n),maximum_bad_scalars=best,
                histogram=histogram,example=example,
                evidence='exhaustive fixed small abstract-code model only')


if __name__ == '__main__':
    result = census(3,3,1)
    print(json.dumps(result,indent=2))
