"""An over-budget abstract code from a rank-two lift of K(4,4,4).

The distance proof uses the exhaustive short-cycle checks below and the
graphical rank argument in the accompanying report. This is not rate half.
"""
import itertools
import json

from probe_multiline_uniform_countermodel import FIRST_PRIME


def main():
    p = FIRST_PRIME
    vertices = range(12)
    edges = [(i,j) for i,j in itertools.combinations(vertices,2) if i//4 != j//4]
    assert len(edges) == 48
    index = {edge:i for i,edge in enumerate(edges)}
    adjacent = {v:[w for w in vertices if w//4 != v//4] for v in vertices}
    cycles = {}
    for length in range(3,7):
        for start in vertices:
            def visit(path):
                last = path[-1]
                if len(path) == length:
                    if start not in adjacent[last] or path[1] > last:
                        return
                    coefficients = {}
                    closed = path+[start]
                    for a,b in zip(closed,closed[1:]):
                        e = index[tuple(sorted((a,b)))]
                        coefficients[e] = 1 if a < b else -1
                    support = frozenset(coefficients)
                    assert support not in cycles
                    a = sum(sign*2**e for e,sign in coefficients.items())
                    b = sum(sign*3**e for e,sign in coefficients.items())
                    assert a and abs(a) < p and abs(b) < p
                    cycles[support] = dict(coefficients=coefficients,syndrome=(a,b),length=length)
                    return
                for nxt in adjacent[last]:
                    if nxt > start and nxt not in path:
                        visit(path+[nxt])
            visit([start])
    short = [(support,cycle) for support,cycle in cycles.items() if cycle['length'] <= 4]
    checked_pairs = 0
    for (s,c),(t,d) in itertools.combinations(short,2):
        if len(s | t) > 6:
            continue
        a,b = c['syndrome']
        aa,bb = d['syndrome']
        assert (a*bb-b*aa) % p
        checked_pairs += 1
    triangles = [(s,c) for s,c in cycles.items() if c['length'] == 3]
    assert len(triangles) == 64
    assert len({b*pow(a % p,-1,p) % p for _,c in triangles
                for a,b in [c['syndrome']]}) == 64

    def vector(c):
        return tuple(c['coefficients'].get(e,0) % p for e in range(48))

    c0,c1 = triangles[0][1],triangles[1][1]
    a0,b0 = c0['syndrome']
    a1,b1 = c1['syndrome']
    inv = pow((a0*b1-b0*a1) % p,-1,p)
    v0,v1 = vector(c0),vector(c1)
    u0 = tuple((b1*x-b0*y)*inv % p for x,y in zip(v0,v1))
    u1 = tuple((-a1*x+a0*y)*inv % p for x,y in zip(v0,v1))

    def syndrome(word):
        incidence = [0]*12
        for e,(i,j) in enumerate(edges):
            incidence[i] += word[e]
            incidence[j] -= word[e]
        return (sum(2**e*word[e] for e in range(48)) % p,
                sum(3**e*word[e] for e in range(48)) % p,
                *tuple(v % p for v in incidence[:11]))

    books = []
    for edge in range(48):
        petals = [(support,c) for support,c in triangles if edge in support]
        assert len(petals) == 4
        for selected in itertools.combinations(petals,3):
            v = [vector(c) for _,c in selected]
            s = [c['syndrome'] for _,c in selected]
            coefficients = [(s[1][0]*s[2][1]-s[1][1]*s[2][0]) % p,
                            (s[2][0]*s[0][1]-s[2][1]*s[0][0]) % p,
                            (s[0][0]*s[1][1]-s[0][1]*s[1][0]) % p]
            assert all(coefficients)
            distance_word = tuple(sum(a*b[e] for a,b in zip(coefficients,v)) % p
                                  for e in range(48))
            support = frozenset(e for e,x in enumerate(distance_word) if x)
            assert syndrome(distance_word) == (0,)*13 and len(support) == 7
            books.append(support)
    assert len(books) == len(set(books)) == 192
    assert all(sum(e in support for support in books) == 28 for e in range(48))
    # Every repeated-coordinate code therefore has distance <=7n/48,
    # by averaging these 192 actual codeword supports.
    assert syndrome(u0) == (1,0)+(0,)*11
    assert syndrome(u1) == (0,1)+(0,)*11
    witnesses = []
    for support,c in triangles:
        a,b = c['syndrome']
        scale = pow(a % p,-1,p)
        gamma = b*scale % p
        error = tuple(v*scale % p for v in vector(c))
        head = tuple((x+gamma*y-z) % p for x,y,z in zip(u0,u1,error))
        assert syndrome(head) == (0,)*13
        assert sum(z != 0 for z in error) == 3
        agreement = tuple(e for e in range(48) if e not in support)
        assert all(head[e] == (u0[e]+gamma*u1[e]) % p for e in agreement)
        witnesses.append(dict(gamma=gamma,head=head,errors=tuple(sorted(support)),
                              agreement=agreement,
                              no_joint='incidence cycle kernel on a triangle has dimension one'))
    # Any three distinct triangle flows are independent: their union has at
    # least five edges, whereas nine occurrences without an exclusive edge
    # could cover at most four. Remove an exclusive flow, then the other two
    # distinct cycles remain independent. Hence no decoded collinear triple.
    for triple in itertools.combinations(triangles,3):
        supports = [entry[0] for entry in triple]
        assert len(set.union(*map(set,supports))) >= 7
        assert any(sum(e in s for s in supports) == 1 for e in set.union(*map(set,supports)))
    errors = [set(w['errors']) for w in witnesses]
    assert all(sum(e in support for support in errors) == 4 for e in range(48))
    cube = sum(len(a | b | c) for a,b,c in itertools.product(errors,repeat=3))
    assert cube == 48*(64**3-60**3)
    assert 48**2*cube+(64*(48-3))**3 == 48**3*64**3
    assert 7*64**3 <= cube+4*3*64**2+7*64
    print(json.dumps(dict(field=p,length=48,dimension=35,distance=7,
                         error_budget=3,witness_count=64,over_budget_required=49,
                         over_budget=True,unique_decoding=True,line_cap=2,
                         parity_check_rows='powers 2 and 3 followed by eleven oriented incidence rows',
                         graph_edges=edges,u0=u0,u1=u1,witnesses=witnesses,
                         cycle_counts={length:sum(c['length'] == length for c in cycles.values())
                                       for length in range(3,7)},
                         checked_nullity_two_cycle_pairs=checked_pairs,
                         seven_coordinate_codeword_supports=len(books),
                         book_support_occurrences_per_coordinate=28,
                         replication_distance_fraction_upper_bound=dict(numerator=7,denominator=48),
                         ordered_union_cube=cube,cube_upper_equality=True,
                         distance_proof='graph rank and checked short-cycle lift conditions',
                         canonical_sponsor_rs_code=False,sponsor_rate_half=False,
                         scope='over-budget abstract countermodel at n=48 D>=7 t=3 only'),indent=2))


if __name__ == '__main__':
    main()
