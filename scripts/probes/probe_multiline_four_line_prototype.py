"""Exact rejection of a rank-seven four-line edge-support prototype."""
import itertools
import json

from probe_multiline_uniform_countermodel import FIRST_PRIME
from probe_multiline_shortening_constraints import rank


def main():
    p = FIRST_PRIME
    alpha,c = (14,15,16,17),(1,-3,3,-1)
    assert sum(c) == 0 and sum(a*b for a,b in zip(alpha,c)) == 0
    columns = []
    for i,j in itertools.combinations(range(4),2):
        for x,y in itertools.product(range(3*i+1,3*i+4),range(3*j+1,3*j+4)):
            row = [0]*8
            a,b = c[j]*(alpha[j]-y),-c[i]*(alpha[i]-x)
            row[2*i],row[2*i+1] = -x*a,a
            row[2*j],row[2*j+1] = -y*b,b
            assert sum(row[2*k]*c[k]+row[2*k+1]*c[k]*alpha[k] for k in range(4)) == 0
            columns.append(tuple(value % p for value in row))
    words = [[column[j] for column in columns] for j in range(8)]
    assert len(columns) == 54 and rank(words,p) == 7
    code = [[(words[j][x]-words[0][x]) % p for x in range(54)] for j in (2,4,6)]
    code += [[(words[j][x]-words[1][x]) % p for x in range(54)] for j in (3,5)]
    assert rank(code,p) == 5
    assert rank(code+words[:2],p) == 7
    errors = []
    for i in range(4):
        for gamma in range(3*i+1,3*i+4):
            error = [(a+gamma*b) % p for a,b in zip(words[2*i],words[2*i+1])]
            assert sum(value != 0 for value in error) == 18
            head = [(a+gamma*b-e) % p for a,b,e in zip(words[0],words[1],error)]
            assert rank(code+[head],p) == 5
            T = [x for x,value in enumerate(error) if not value]
            restricted = [[row[x] for x in T] for row in code]
            assert any(rank(restricted+[[row[x] for x in T]],p) > rank(restricted,p) for row in words[:2])
            errors.append(error)
    assert rank(errors,p) == 7
    distance_word = [(a+b-d-e) % p for a,b,d,e in zip(words[0],words[1],words[2],words[3])]
    distance_upper = sum(value != 0 for value in distance_word)
    assert distance_upper == 39 and rank(code+[distance_word],p) == 5
    assert 7*18 >= 3*distance_upper
    print(json.dumps(dict(field=p,length=54,code_dimension=5,witness_count=12,
                         error_budget=18,error_span_rank=7,
                         scalar_groups=[list(range(3*i+1,3*i+4)) for i in range(4)],
                         no_joint_explanation_checked=True,
                         distance_upper_bound=distance_upper,distance_witness=distance_word,
                         exact_minimum_distance='not computed because an upper certificate already rejects the target regime',
                         cap_domain_7t_less_3D_possible=False,
                         conclusion='dependent four-line geometry exists here but its distance is insufficient',
                         canonical_sponsor_rs_code=False,new_lean_theorem=False,
                         threshold_improvement=False),indent=2))


if __name__ == '__main__':
    main()
