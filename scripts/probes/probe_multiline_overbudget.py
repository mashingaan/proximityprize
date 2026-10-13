"""Complete fixed-code F17 over-budget search using quotient support syndromes."""
import itertools
import json
import sys

import probe_multiline_rank_two as q
from probe_multiline_uniform_countermodel import determinant


def configure(p,columns):
    q.P,q.K,q.N = p,4,8
    q.G = columns
    q.SUPPORTS = list(itertools.combinations(range(8),6))
    q.SOLVERS = {support: q.inverse([columns[x] for x in support[:4]])
                 for support in q.SUPPORTS}
    assert all(determinant([columns[x] for x in support],p)
               for support in itertools.combinations(range(8),4))
    kernels = []
    for support in q.SUPPORTS:
        residuals = []
        for j in range(4):
            word = (0,)*4+tuple(int(i == j) for i in range(4))
            head = tuple(sum(v*word[x] for v,x in zip(row,support[:4])) % p
                         for row in q.SOLVERS[support])
            residuals.append(tuple((word[x]-sum(v*w for v,w in zip(columns[x],head))) % p
                                   for x in support[4:]))
        kernels.append((support,tuple(tuple(residuals[j][i] for j in range(4))
                                      for i in range(2))))
    return kernels


def optimized_pencil(basis,kernels):
    p = q.P
    grouped = {}
    for support,matrix in kernels:
        a = tuple(sum(v*w for v,w in zip(row,basis[0])) % p for row in matrix)
        b = tuple(sum(v*w for v,w in zip(row,basis[1])) % p for row in matrix)
        if a == (0,0) and b == (0,0):
            continue  # Both rows have a joint explanation on this support.
        if (a[0]*b[1]-a[1]*b[0]) % p:
            continue
        if b == (0,0):
            direction = (0,1)
        else:
            j = 0 if b[0] else 1
            direction = (1,-a[j]*pow(b[j],-1,p) % p)
        word = tuple((direction[0]*v+direction[1]*w) % p
                     for v,w in zip(q.lift(basis[0]),q.lift(basis[1])))
        head = q.decode(word,support)
        assert head is not None
        witness = dict(head=head,agreement=support,
                       errors=tuple(x for x in range(8) if x not in support))
        if direction not in grouped:
            grouped[direction] = dict(direction=direction,head=head,witnesses=[])
        assert grouped[direction]['head'] == head
        grouped[direction]['witnesses'].append(witness)
    return [grouped[d] for d in sorted(grouped,key=lambda d: (d[0] == 0,d[1]))]


def signature(bad):
    return {b['direction']: (b['head'],tuple(sorted(w['agreement'] for w in b['witnesses'])))
            for b in bad}


def calibration():
    p = 7
    columns = [tuple(pow(x,j,p) for j in range(4)) for x in range(p)]
    columns.append((0,0,0,1))
    kernels = configure(p,columns)
    count = 0
    for basis in q.planes():
        fast = optimized_pencil(basis,kernels)
        direct = q.pencil(*map(q.lift,basis))
        assert signature(fast) == signature(direct)
        count += 1
    assert count == 2850
    return count


def census():
    p = 17
    columns = [tuple(pow(x,j,p) for j in range(4)) for x in range(1,7)]
    columns += [(0,0,1,0),(0,0,0,1)]
    kernels = configure(p,columns)
    count = 0
    histogram = {}
    maximum = -1
    best = None
    directions = [(1,gamma) for gamma in range(p)]+[(0,1)]
    for basis in q.planes():
        bad = optimized_pencil(basis,kernels)
        size = len(bad)
        if size:
            histogram[size-1] = histogram.get(size-1,0)+size
        if size < p+1:
            histogram[size] = histogram.get(size,0)+p+1-size
        finite_size = min(p,size)
        if finite_size > maximum:
            omitted = next((d for d in directions if d not in {b['direction'] for b in bad}),directions[0])
            remaining = [i for i,b in enumerate(bad) if b['direction'] != omitted]
            best = dict(quotient_basis=basis,u0=q.lift(basis[0]),u1=q.lift(basis[1]),
                        omitted_projective_direction=omitted,bad=bad,
                        retained_bad_indices=remaining,
                        retained_three_head_lines=[line for line in q.three_lines(bad)
                                                   if len(set(line).intersection(remaining)) >= 3])
            maximum = finite_size
        count += 1
        if count % 10000 == 0:
            print(f'F17 planes checked {count}, current maximum {maximum}',file=sys.stderr,flush=True)
    expected = ((p**4-1)*(p**4-p)) // ((p**2-1)*(p**2-p))
    assert count == expected == 89030
    assert sum(histogram.values()) == (p+1)*count
    assert signature(best['bad']) == signature(q.pencil(best['u0'],best['u1']))
    direct_certificate = q.independent_certificate(best)
    assert len(direct_certificate['bad']) == maximum
    return dict(field=p,length=8,dimension=4,distance=5,error_budget=2,
                generator_columns=columns,quotient_planes=count,affine_charts=(p+1)*count,
                affine_chart_histogram=histogram,maximum_bad_scalars=maximum,
                over_budget_required=9,over_budget_found=maximum >= 9,
                dependent_quotient_pairs_bad_scalar_upper_bound=1,
                maximizer=direct_certificate,
                scope='all stacks for this fixed abstract code only, not all codes or sponsor parameters')


if __name__ == '__main__':
    calibrated = calibration()
    result = census()
    print(json.dumps(dict(calibration_planes=calibrated,overbudget_census=result),indent=2))
