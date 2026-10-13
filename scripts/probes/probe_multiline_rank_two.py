"""Complete quotient-pencil census for one abstract [6,2,5] code over F5.

This is not an optimization over all codes or sponsor parameters.
"""
import itertools
import json

P = 5
G = [(1, x) for x in range(P)] + [(0, 1)]
N = len(G)
T = 2
SUPPORTS = list(itertools.combinations(range(N), N-T))


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


def decode(word, support):
    i,j = support[:2]
    a,b = G[i]
    c,d = G[j]
    det = (a*d-b*c) % P
    assert det
    inv = pow(det,-1,P)
    head = ((d*word[i]-b*word[j])*inv % P,
            (a*word[j]-c*word[i])*inv % P)
    if all((G[x][0]*head[0]+G[x][1]*head[1]) % P == word[x]
           for x in support):
        return head
    return None


def lift(q):
    # The first two generator columns are independent. Subtracting a codeword
    # sets these coordinates to zero and identifies the quotient with F5^4.
    return (0,0) + tuple(q)


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


def main():
    distance = min(sum((a*x+b*y) % P != 0 for x,y in G)
                   for a,b in itertools.product(range(P),repeat=2) if a or b)
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
    assert count == gaussian == 806
    assert sum(histogram.values()) == 6*count
    print(json.dumps(dict(field=P,length=N,dimension=2,distance=distance,
                         generator_columns=G,error_budget=T,
                         rank_two_quotient_planes=count,
                         affine_chart_count=6*count,
                         finite_bad_scalar_histogram=histogram,
                         maximum_bad_scalars_rank_two=maximum,example=example,
                         maximum_coexisting_three_head_lines=maximum_lines,
                         multiline_example=multiline_example,
                         dependent_quotient_pairs_bad_scalar_upper_bound=1,
                         evidence='complete fixed-code quotient-plane census, not all codes'),
                     indent=2))


if __name__ == '__main__':
    main()
