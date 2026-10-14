"""Exact first-field three-pencil rank-six certificate in the abstract model."""
import itertools
import json

from probe_multiline_uniform_countermodel import FIRST_PRIME
from probe_multiline_shortening_constraints import rank


def solve(rows,values,p):
    a = [list(row)+[value] for row,value in zip(rows,values)]
    for j in range(len(a)):
        pivot = next(i for i in range(j,len(a)) if a[i][j] % p)
        a[j],a[pivot] = a[pivot],a[j]
        inv = pow(a[j][j] % p,-1,p)
        a[j] = [value*inv % p for value in a[j]]
        for i in range(len(a)):
            if i != j:
                factor = a[i][j]
                a[i] = [(x-factor*y) % p for x,y in zip(a[i],a[j])]
    return [row[-1] for row in a]


def main():
    p = FIRST_PRIME
    columns = [(pow(32,i,p),pow(32,10*i,p))+tuple(int(g == (i-1)//3) for g in range(3))
               for i in range(1,10)]
    assert rank(columns,p) == 5
    for S in itertools.combinations(range(9),4):
        assert rank([columns[x] for x in S],p) == 4
    assert rank(columns[:5],p) == 4
    basis = []
    for x in range(9):
        if rank([columns[j] for j in basis+[x]],p) > len(basis):
            basis.append(x)
    assert len(basis) == 5
    matrix = [[columns[j][i] for j in basis] for i in range(5)]
    received = []
    for row in range(2):
        values = solve(matrix,[int(i == row) for i in range(5)],p)
        word = [0]*9
        for x,value in zip(basis,values):
            word[x] = value
        received.append(word)
    witnesses = []
    errors = []
    L = [(1,0,0,0,0),(0,1,0,0,0)]
    for group in range(3):
        for i,j in itertools.combinations(range(3*group,3*group+3),2):
            da = (columns[i][0]-columns[j][0]) % p
            db = (columns[i][1]-columns[j][1]) % p
            coefficient = pow(da,-1,p)
            gamma = db*coefficient % p
            error = [0]*9
            error[i],error[j] = coefficient,-coefficient % p
            assert [sum(columns[x][k]*error[x] for x in range(9)) % p for k in range(5)] == [1,gamma,0,0,0]
            assert rank([columns[i],columns[j]]+L,p) == 3
            errors.append(error)
            witnesses.append(dict(gamma=gamma,error_support=[i,j],error=error,group=group))
    assert len(set(w['gamma'] for w in witnesses)) == 9
    assert rank(errors,p) == 6
    ranks = [rank(errors[3*g:3*g+3],p) for g in range(3)]
    assert ranks == [2,2,2]
    triples = [list(S) for S in itertools.combinations(range(9),3)
               if rank([errors[x] for x in S],p) == 2]
    assert triples == [[0,1,2],[3,4,5],[6,7,8]]
    assert 7*2 < 3*5
    print(json.dumps(dict(field=p,length=9,code_dimension=4,distance=5,error_budget=2,
                         parity_columns=columns,u0=received[0],u1=received[1],
                         witnesses=witnesses,error_span_rank=6,pencil_ranks=ranks,
                         three_head_line_partition=triples,
                         four_column_independence_checks=126,
                         no_joint_explanation='each two-column syndrome span intersects received plane in dimension one',
                         over_budget=False,canonical_sponsor_rs_code=False,
                         scope='nine witnesses in an abstract length-nine first-field linear code',
                         universal_proof='handwritten three-pencil rank independence',
                         new_lean_theorem=False,threshold_improvement=False),indent=2))


if __name__ == '__main__':
    main()
