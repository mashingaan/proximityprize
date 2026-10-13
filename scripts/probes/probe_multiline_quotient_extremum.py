"""Sharp abstract n=8, t=2, distance>=5 model over the literal first field.

The upper bound is proved in the accompanying quotient geometry argument.
This script checks its attaining certificate, not a sponsor-length solution.
"""
import itertools
import json

from probe_multiline_uniform_countermodel import FIRST_PRIME,determinant,solve


def main():
    p = FIRST_PRIME
    labels = [0,0,0,1,1,1,2,2]
    columns = [(pow(32,i,p),pow(32,10*i,p),1,label)
               for i,label in enumerate(labels,1)]
    minors = [determinant([columns[x] for x in support],p)
              for support in itertools.combinations(range(8),4)]
    assert len(minors) == 70 and all(minors)
    # H maps words to syndromes. Its first four columns form an invertible map.
    first_matrix = [tuple(columns[j][i] for j in range(4)) for i in range(4)]
    u0 = solve(first_matrix,(1,0,0,0),p)+(0,)*4
    u1 = solve(first_matrix,(0,1,0,0),p)+(0,)*4

    def syndrome(word):
        return tuple(sum(columns[x][j]*word[x] for x in range(8)) % p
                     for j in range(4))

    assert syndrome(u0) == (1,0,0,0)
    assert syndrome(u1) == (0,1,0,0)
    witnesses = []
    for i,j in itertools.combinations(range(8),2):
        if labels[i] != labels[j]:
            continue
        da = (columns[i][0]-columns[j][0]) % p
        db = (columns[i][1]-columns[j][1]) % p
        assert da
        coefficient = pow(da,-1,p)
        gamma = db*coefficient % p
        error = [0]*8
        error[i],error[j] = coefficient,-coefficient % p
        received = tuple((a+gamma*b) % p for a,b in zip(u0,u1))
        head = tuple((a-b) % p for a,b in zip(received,error))
        assert syndrome(head) == (0,0,0,0)
        support = tuple(x for x in range(8) if x not in (i,j))
        assert all(head[x] == received[x] for x in support)
        # The span of these two columns projects to a nonzero one-dimensional
        # space in the last two coordinates. It cannot contain the whole
        # syndrome pencil spanned by e0,e1, so no joint explanation exists.
        assert columns[i][2:] == columns[j][2:] and columns[i][2:] != (0,0)
        assert determinant([columns[i],columns[j],(1,0,0,0),(0,1,0,0)],p) == 0
        witnesses.append(dict(gamma=gamma,head=head,errors=(i,j),agreement=support,
                              no_joint='pencil not contained in error-support span'))
    assert len(witnesses) == len({w['gamma'] for w in witnesses}) == 7
    # A dependence on any five columns attains weight five, because all four
    # column minors are nonzero. Compute such a dependence explicitly.
    rhs = tuple(-columns[4][j] % p for j in range(4))
    distance_word = solve(first_matrix,rhs,p)+(1,0,0,0)
    assert syndrome(distance_word) == (0,0,0,0)
    assert sum(v != 0 for v in distance_word) == 5
    # Each pair of distinct scalars forbids at most one shear coefficient.
    # Twenty-one pairs therefore leave a valid choice among 0,...,21.
    shear = next(value for value in range(22)
                 if len({tuple((a+w['gamma']*value*b) % p
                               for a,b in zip(w['head'],distance_word))
                         for w in witnesses}) == 7)
    u1 = tuple((a+shear*b) % p for a,b in zip(u1,distance_word))
    assert syndrome(u1) == (0,1,0,0)
    for witness in witnesses:
        witness['head'] = tuple((a+witness['gamma']*shear*b) % p
                                for a,b in zip(witness['head'],distance_word))
        assert syndrome(witness['head']) == (0,0,0,0)
        assert all(witness['head'][x] == (u0[x]+witness['gamma']*u1[x]) % p
                   for x in witness['agreement'])
    assert len({w['head'] for w in witnesses}) == 7
    print(json.dumps(dict(field=p,length=8,dimension=4,error_budget=2,distance=5,
                         parity_check_columns=columns,nonzero_four_column_minors=70,
                         projected_fiber_sizes=(3,3,2),u0=u0,u1=u1,witnesses=witnesses,
                         codeword_shear_coefficient=shear,codeword_shear=distance_word,
                         attained_bad_scalar_count=7,
                         universal_abstract_upper_bound=7,
                         upper_bound_evidence='handwritten quotient projection proof',
                         full_sponsor_length=False,canonical_sponsor_rs_code=False,
                         over_budget=False),indent=2))


if __name__ == '__main__':
    main()
