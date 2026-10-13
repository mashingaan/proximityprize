"""Field-uniform two-line abstract MDS certificate, not a sponsor RS stack."""
import itertools
import json

FIRST_PRIME = 365375409332725729550921208179070755120141565953


def determinant(rows,p):
    a = [list(row) for row in rows]
    value = 1
    for j in range(len(a)):
        pivot = next((i for i in range(j,len(a)) if a[i][j] % p),None)
        if pivot is None:
            return 0
        if pivot != j:
            a[j],a[pivot] = a[pivot],a[j]
            value = -value
        z = a[j][j] % p
        value = value*z % p
        inv = pow(z,-1,p)
        for i in range(j+1,len(a)):
            factor = a[i][j]*inv % p
            a[i] = [(v-factor*w) % p for v,w in zip(a[i],a[j])]
    return value % p


def solve(rows,values,p):
    a = [list(row)+[value] for row,value in zip(rows,values)]
    for j in range(4):
        pivot = next(i for i in range(j,4) if a[i][j] % p)
        a[j],a[pivot] = a[pivot],a[j]
        inv = pow(a[j][j] % p,-1,p)
        a[j] = [v*inv % p for v in a[j]]
        for i in range(4):
            if i != j:
                factor = a[i][j]
                a[i] = [(v-factor*w) % p for v,w in zip(a[i],a[j])]
    return tuple(row[-1] for row in a)


def certificate(p):
    assert p > 15
    columns = [tuple(pow(x,j,p) for j in range(4)) for x in range(1,7)]
    columns += [(0,0,1,0),(0,0,0,1)]
    minors = [determinant([columns[x] for x in support],p)
              for support in itertools.combinations(range(8),4)]
    assert len(minors) == 70 and all(minors)

    def word(head):
        return tuple(sum(a*b for a,b in zip(head,column)) % p for column in columns)

    # A cubic with roots 1,2,3 has exactly three zero coordinates.
    distance_word = word((-6,11,-6,1))
    assert sum(v != 0 for v in distance_word) == 5
    # The checked minors prove every nonzero codeword has weight at least 5.
    u0 = tuple([-1 % p,-2 % p,-3 % p,0,0,0,0,0])
    u1 = (2,2,2,1,1,1,0,0)
    first_joint = (3,4,5,6,7)
    second_joint = (0,1,2,6,7)
    witnesses = []
    for gamma in range(1,7):
        head = (gamma,0,0,0) if gamma <= 3 else (2*gamma % p,-1 % p,0,0)
        joint = first_joint if gamma <= 3 else second_joint
        support = tuple(sorted(joint+(gamma-1,)))
        errors = tuple(x for x in range(8) if x not in support)
        received = tuple((a+gamma*b) % p for a,b in zip(u0,u1))
        assert len(errors) == 2
        assert all(word(head)[x] == received[x] for x in support)
        candidate = solve([columns[x] for x in support[:4]],
                          [u0[x] for x in support[:4]],p)
        assert any(word(candidate)[x] != u0[x] for x in support)
        witnesses.append(dict(gamma=gamma,head=head,agreement=support,errors=errors,
                              private=(gamma-1,),no_joint='u0 restriction outside code image'))
    assert len({tuple(w['head']) for w in witnesses}) == 6
    lines = [dict(scalars=(1,2,3),intercept=(0,0,0,0),direction=(1,0,0,0),
                  joint=first_joint),
             dict(scalars=(4,5,6),intercept=(0,-1 % p,0,0),direction=(2,0,0,0),
                  joint=second_joint)]
    for line in lines:
        actual_joint = tuple(x for x in range(8)
                             if word(line['intercept'])[x] == u0[x]
                             and word(line['direction'])[x] == u1[x])
        assert actual_joint == line['joint']
        for witness in witnesses:
            if witness['gamma'] in line['scalars']:
                assert tuple((a+witness['gamma']*b) % p
                             for a,b in zip(line['intercept'],line['direction'])) == witness['head']
    assert 7*2 < 3*5
    errors = [set(w['errors']) for w in witnesses]
    for i,j in itertools.combinations(range(6),2):
        assert 5 <= len(errors[i] | errors[j])+2
    for i,j,k in itertools.combinations(range(6),3):
        if not (k < 3 or i >= 3):
            assert len(errors[i] | errors[j] | errors[k]) == 5
    union_cube = sum(len(errors[i] | errors[j] | errors[k])
                     for i,j,k in itertools.product(range(6),repeat=3))
    assert union_cube == 912
    assert 5*6**3 <= union_cube+4*2*6**2+5*6
    assert 8**2*union_cube+(6*(8-2))**3 <= 8**3*6**3
    return dict(field=p,length=8,dimension=4,distance=5,error_budget=2,
                generator_columns=columns,nonzero_four_column_minors=len(minors),
                u0=u0,u1=u1,witnesses=witnesses,lines=lines,
                ordered_collinear_triples=12,ordered_union_cube=union_cube,
                literal_sponsor_length=False,canonical_sponsor_rs_code=False,
                over_budget=False,scope='six witnesses in a fixed abstract MDS code')


def weighted_certificate(base):
    n = 1073741824
    t = 221512373
    private_weight = t//2
    remainder = n-6*private_weight
    weights = [private_weight]*6+[remainder//2,remainder-remainder//2]
    # Any three column zeros are attainable and any four are impossible,
    # as certified by the seventy nonzero minors of the base generator.
    distance = n-sum(sorted(weights,reverse=True)[:3])
    required_distance = 536870913
    assert sum(weights) == n and distance >= required_distance
    for witness in base['witnesses']:
        assert sum(weights[x] for x in witness['errors']) <= t
    assert 7*t < 3*required_distance
    return dict(field=base['field'],length=n,dimension=4,block_weights=weights,
                error_budget=t,actual_error_support=2*private_weight,
                exact_distance=distance,required_distance=required_distance,
                joint_core_cardinality=n-3*private_weight,
                private_cardinality=private_weight,witness_count=6,
                required_over_budget_witness_count=n+1,
                over_budget=False,canonical_sponsor_rs_code=False,
                scope='literal field and length, six witnesses only in a replicated abstract code')


if __name__ == '__main__':
    certificates = [certificate(p) for p in (17,101,65537,2147483647,FIRST_PRIME)]
    print(json.dumps(dict(certificates=certificates,
                         weighted_literal_parameter_certificate=weighted_certificate(certificates[-1]),
                         symbolic_hypothesis='prime characteristic greater than 15',
                         evidence='exact minors and witness verification, handwritten uniform proof'),
                     indent=2))
