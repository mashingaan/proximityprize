"""Exact shortening checks and a finite-field obstruction to a rank relaxation."""
import itertools
import json

from probe_multiline_uniform_countermodel import FIRST_PRIME


def rank(rows,p):
    a = [list(row) for row in rows]
    r = 0
    for j in range(len(a[0]) if a else 0):
        pivot = next((i for i in range(r,len(a)) if a[i][j] % p),None)
        if pivot is None:
            continue
        a[r],a[pivot] = a[pivot],a[r]
        inv = pow(a[r][j] % p,-1,p)
        a[r] = [v*inv % p for v in a[r]]
        for i in range(r+1,len(a)):
            factor = a[i][j]
            a[i] = [(v-factor*w) % p for v,w in zip(a[i],a[r])]
        r += 1
        if r == len(a):
            break
    return r


def small_shortening():
    projected = [(1,label) for label in (0,0,0,1,1,1,2,2)]
    histogram = {}
    third_weight = 9
    for size in range(9):
        nullities = []
        for support in itertools.combinations(range(8),size):
            nullity = size-rank([projected[x] for x in support],FIRST_PRIME)
            nullities.append(nullity)
            if nullity >= 3:
                third_weight = min(third_weight,size)
        histogram[size] = dict(minimum=min(nullities),maximum=max(nullities))
    assert third_weight == 5
    assert histogram[4] == dict(minimum=2,maximum=2)
    assert histogram[5] == dict(minimum=3,maximum=3)
    return dict(field=FIRST_PRIME,length=8,supercode_dimension=6,
                third_generalized_support_weight=third_weight,
                shortening_dimensions=histogram,
                scope='all coordinate supports of the explicit length-eight quotient certificate')


def finite_field_obstruction():
    words = list(itertools.product(range(2),repeat=4))
    surjections = 0
    valid = 0
    best = 0
    for rows in itertools.product(words,repeat=2):
        if rank(rows,2) != 2:
            continue
        surjections += 1
        kernel = [word for word in words
                  if all(sum(a*b for a,b in zip(row,word)) % 2 == 0 for row in rows)]
        assert len(kernel) == 4
        distance = min(sum(word) for word in kernel if any(word))
        best = max(best,distance)
        valid += distance >= 3
    assert surjections == 210 and valid == 0 and best == 2
    # The full ambient K=F2^4 has third support weight three and dimension four,
    # exactly the proposed relaxed Singleton equality, but no suitable C.
    return dict(field=2,length=4,supercode_dimension=4,
                third_generalized_support_weight=3,required_code_dimension=2,
                required_code_distance=3,rank_two_surjections=surjections,
                suitable_kernels=valid,best_kernel_distance=best,
                conclusion='third-support-weight condition alone does not certify a codimension-two code')


def literal_dimensions():
    n,k,D = 1073741824,536870912,536870913
    assert D == n-k+1
    dimension = k+2
    projected_rank = n-dimension
    assert projected_rank == D-3
    assert dimension-(n-(D-1)) == 2
    assert dimension-(n-D) == 3
    return dict(length=n,code_dimension=k,required_distance=D,
                conditional_supercode_dimension=dimension,
                conditional_projected_rank=projected_rank,
                conditional_third_support_weight=D,
                hypotheses=['code dimension k and minimum distance n-k+1',
                            'received rows independent modulo the code'],
                evidence='integer instantiation of the handwritten dimension proof, no full matrix census')


if __name__ == '__main__':
    print(json.dumps(dict(small_shortening=small_shortening(),
                         finite_field_obstruction=finite_field_obstruction(),
                         literal_dimension_ledger=literal_dimensions()),indent=2))
