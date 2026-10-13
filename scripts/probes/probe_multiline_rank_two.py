"""Complete quotient-pencil census for fixed abstract codes with quotient dim 4.

This is not an optimization over all codes or sponsor parameters.
"""
import itertools
import json

P = 5
G = [(1, x) for x in range(P)] + [(0, 1)]
N = len(G)
K = 2
T = 2
SUPPORTS = list(itertools.combinations(range(N), N-T))
SOLVERS = {}


def rank(rows):
    a = [list(row) for row in rows]
    r = 0
    for j in range(len(a[0]) if a else 0):
        pivot = next((i for i in range(r, len(a)) if a[i][j] % P), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        z = pow(a[r][j] % P, -1, P)
        a[r] = [x*z % P for x in a[r]]
        for i in range(len(a)):
            if i != r:
                z = a[i][j]
                a[i] = [(x-z*y) % P for x,y in zip(a[i],a[r])]
        r += 1
        if r == len(a):
            break
    return r


def inverse(rows):
    a = [list(row)+[int(i == j) for j in range(K)]
         for i,row in enumerate(rows)]
    for j in range(K):
        pivot = next(i for i in range(j,K) if a[i][j] % P)
        a[j],a[pivot] = a[pivot],a[j]
        inv = pow(a[j][j],-1,P)
        a[j] = [v*inv % P for v in a[j]]
        for i in range(K):
            if i != j:
                z = a[i][j]
                a[i] = [(v-z*w) % P for v,w in zip(a[i],a[j])]
    return [row[K:] for row in a]


def decode(word, support):
    inv = SOLVERS[support]
    head = tuple(sum(v*word[x] for v,x in zip(row,support[:K])) % P
                 for row in inv)
    if all(sum(v*w for v,w in zip(G[x],head)) % P == word[x]
           for x in support):
        return head
    return None


def lift(q):
    # The first K generator columns are independent. Subtracting a codeword
    # sets these coordinates to zero and identifies the quotient with F5^4.
    return (0,)*K + tuple(q)


def planes():
    for pivots in itertools.combinations(range(4),2):
        free = [(i,j) for i,pivot in enumerate(pivots)
                for j in range(pivot+1,4) if j not in pivots]
        for values in itertools.product(range(P),repeat=len(free)):
            rows = [[0]*4 for _ in range(2)]
            for i,pivot in enumerate(pivots):
                rows[i][pivot] = 1
            for (i,j),value in zip(free,values):
                rows[i][j] = value
            yield tuple(map(tuple,rows))


def pencil(u0,u1):
    directions = [(1,gamma) for gamma in range(P)] + [(0,1)]
    bad = []
    for s0,s1 in directions:
        word = tuple((s0*a+s1*b) % P for a,b in zip(u0,u1))
        witnesses = []
        for support in SUPPORTS:
            head = decode(word,support)
            if head is None:
                continue
            if decode(u0,support) is not None and decode(u1,support) is not None:
                continue
            witnesses.append(dict(head=head,agreement=support,
                                  errors=tuple(x for x in range(N) if x not in support)))
        if witnesses:
            heads = {w['head'] for w in witnesses}
            assert len(heads) == 1  # 2t < distance gives unique decoding.
            bad.append(dict(direction=(s0,s1),head=witnesses[0]['head'],
                            witnesses=witnesses))
    return bad


def three_lines(bad):
    points = [tuple(b['direction'])+tuple(b['head']) for b in bad]
    lines = set()
    for triple in itertools.combinations(range(len(points)),3):
        if rank([points[i] for i in triple]) != 2:
            continue
        members = tuple(i for i,p in enumerate(points)
                        if rank([points[triple[0]],points[triple[1]],p]) == 2)
        # Each finite affine chart has an outside witness when it has >3
        # points. Record projective lines before chart deletion.
        lines.add(members)
    return sorted(lines)


def independent_certificate(record):
    omitted = record['omitted_projective_direction']
    base = next(v for v in [(1,g) for g in range(P)]+[(0,1)] if v != omitted)
    old0,old1 = record['u0'],record['u1']
    u0 = tuple((base[0]*a+base[1]*b) % P for a,b in zip(old0,old1))
    u1 = tuple((omitted[0]*a+omitted[1]*b) % P for a,b in zip(old0,old1))
    words = [(head,tuple(sum(a*b for a,b in zip(head,column)) % P
                         for column in G))
             for head in itertools.product(range(P),repeat=K)]
    images = {support: {tuple(word[x] for x in support) for _,word in words}
              for support in SUPPORTS}
    bad = []
    for gamma in range(P):
        received = tuple((a+gamma*b) % P for a,b in zip(u0,u1))
        witnesses = []
        for head,word in words:
            agreement = tuple(x for x in range(N) if word[x] == received[x])
            if len(agreement) < N-T:
                continue
            for support in itertools.combinations(agreement,N-T):
                if (tuple(u0[x] for x in support) in images[support]
                        and tuple(u1[x] for x in support) in images[support]):
                    continue
                witnesses.append(dict(head=head,agreement=support,
                                      errors=tuple(x for x in range(N) if x not in support)))
        if witnesses:
            assert len({w['head'] for w in witnesses}) == 1
            bad.append(dict(direction=(1,gamma),head=witnesses[0]['head'],
                            witnesses=witnesses))
    assert len(bad) == len(record['retained_bad_indices'])
    lines = three_lines(bad)
    assert len(lines) == len(record['retained_three_head_lines'])
    return dict(u0=u0,u1=u1,bad=bad,three_head_lines=lines,
                verifier='enumerate every codeword and restricted code image')


def census(p,k):
    global P,G,N,K,SUPPORTS,SOLVERS
    P,K = p,k
    G = [tuple(pow(x,j,P) for j in range(K)) for x in range(P)]
    G.append((0,)*(K-1)+(1,))
    N = len(G)
    assert N-K == 4
    SUPPORTS = list(itertools.combinations(range(N),N-T))
    SOLVERS = {support: inverse([G[x] for x in support[:K]])
               for support in SUPPORTS}
    distance = min(sum(sum(v*w for v,w in zip(head,column)) % P != 0
                       for column in G)
                   for head in itertools.product(range(P),repeat=K) if any(head))
    assert distance == 5 and 7*T < 3*distance
    count = 0
    histogram = {}
    maximum = -1
    example = None
    maximum_lines = 0
    multiline_example = None
    for basis in planes():
        count += 1
        u0,u1 = map(lift,basis)
        bad = pencil(u0,u1)
        lines = three_lines(bad)
        directions = [(1,gamma) for gamma in range(P)] + [(0,1)]
        for omitted in directions:
            remaining = [i for i,b in enumerate(bad) if b['direction'] != omitted]
            size = len(remaining)
            histogram[size] = histogram.get(size,0)+1
            active_lines = [line for line in lines
                            if len(set(line).intersection(remaining)) >= 3]
            assert all(len(set(line).intersection(remaining)) <= 3
                       for line in active_lines)
            record = dict(quotient_basis=basis,u0=u0,u1=u1,
                          omitted_projective_direction=omitted,bad=bad,
                          retained_bad_indices=remaining,
                          retained_three_head_lines=active_lines)
            if size > maximum:
                maximum,example = size,record
            if len(active_lines) > maximum_lines:
                maximum_lines,multiline_example = len(active_lines),record
    gaussian = ((P**4-1)*(P**4-P)) // ((P**2-1)*(P**2-P))
    assert count == gaussian
    assert sum(histogram.values()) == (P+1)*count
    return dict(field=P,length=N,dimension=K,distance=distance,
                         generator_columns=G,error_budget=T,
                         rank_two_quotient_planes=count,
                         affine_chart_count=(P+1)*count,
                         finite_bad_scalar_histogram=histogram,
                         maximum_bad_scalars_rank_two=maximum,example=example,
                         independent_maximizer=independent_certificate(example),
                         maximum_coexisting_three_head_lines=maximum_lines,
                         multiline_example=multiline_example,
                         independent_line_maximizer=(independent_certificate(multiline_example)
                                                     if multiline_example else None),
                         dependent_quotient_pairs_bad_scalar_upper_bound=1,
                         evidence='complete fixed-code quotient-plane census, not all codes')


if __name__ == '__main__':
    print(json.dumps(dict(models=[census(5,2),census(7,4)]),indent=2))
