"""Linear algebra sanity check for the global relation-core formula.

This example is not a bad-witness code construction.
"""
import json

from probe_multiline_shortening_constraints import rank


def main():
    p = 17
    inv3 = pow(3,-1,p)
    pencils = [[[int(j == 2*i+k) for j in range(6)] for k in range(2)]
               for i in range(3)]
    pencils.append([[inv3*int(j % 2 == k) % p for j in range(6)] for k in range(2)])
    rows = [row for pencil in pencils for row in pencil]
    R = rank(rows,p)
    relations = [[-inv3 if j in (k,2+k,4+k) else int(j == 6+k) for j in range(8)]
                 for k in range(2)]
    assert R == 6 and rank(relations,p) == 2
    assert all(sum(relation[j]*rows[j][x] for j in range(8)) % p == 0
               for relation in relations for x in range(6))
    projection_ranks = [rank([[row[2*i],row[2*i+1]] for row in relations],p)
                        for i in range(4)]
    assert projection_ranks == [2,2,2,2]
    core_rank = sum(projection_ranks)-rank(relations,p)
    assert core_rank == R
    supports = [{j for j in range(6) if any(row[j] for row in pencil)} for pencil in pencils]
    shared = {j for j in range(6) if sum(j in support for support in supports) >= 2}
    assert shared == set(range(6))
    print(json.dumps(dict(field=p,pencil_count=4,total_rank=R,relation_dimension=2,
                         relation_projection_ranks=projection_ranks,relation_core_rank=core_rank,
                         shared_support=sorted(shared),
                         universal_formula='core rank = sum_i projection_rank_i - relation_dimension',
                         shortening_bound='shared support >= D+core_rank-3 when core_rank>=3',
                         scope='linear algebra identity test, not a valid bad-witness example',
                         new_lean_theorem=False,threshold_improvement=False),indent=2))


if __name__ == '__main__':
    main()
