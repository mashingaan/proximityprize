"""Exhaustive finite-field abstract-code census, not a sponsor-scale certificate."""
import itertools
import json


def geometry(p, u0, u1, bad):
    selected = [(b['gamma'], b['witnesses'][0]['head']) for b in bad]
    triples = []
    for a,b,c in itertools.combinations(selected,3):
        if ((b[1]-a[1])*(c[0]-a[0])
                -(c[1]-a[1])*(b[0]-a[0])) % p:
            continue
        direction = (b[1]-a[1])*pow((b[0]-a[0]) % p,-1,p) % p
        intercept = (a[1]-a[0]*direction) % p
        joint = [i for i in range(len(u0))
                 if u0[i] == intercept and u1[i] == direction]
        private = {}
        for gamma,head in (a,b,c):
            witness = next(z for z in bad if z['gamma'] == gamma)['witnesses'][0]
            private[str(gamma)] = [i for i in witness['agreement'] if i not in joint]
        triples.append(dict(scalars=[a[0],b[0],c[0]],intercept=intercept,
                            direction=direction,joint=joint,private=private))
    return dict(selected_heads=selected,collinear_triples=triples,
                selected_head_policy='first valid witness, other choices are retained')


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
                example = dict(u0=list(u0),u1=list(u1),bad=bad,
                               geometry=geometry(p,u0,u1,bad))
    assert sum(histogram.values()) == p**(2*n)
    return dict(field=p,length=n,dimension=1,error_budget=t,
                stacks_checked=p**(2*n),maximum_bad_scalars=best,
                histogram=histogram,example=example,
                evidence='exhaustive fixed small abstract-code model only')


if __name__ == '__main__':
    results = [census(p,3,1) for p in (3,5)]
    assert all(r['maximum_bad_scalars'] == 3 for r in results)
    print(json.dumps(dict(models=results,
                         evidence='two exhaustive fixed models, no sponsor-scale sharpness claim'),
                     indent=2))
