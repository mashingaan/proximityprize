"""Exact certificate checks for a general multi-line rank-shortening bound.

The universal proof is in multi-line-extremal-model.md.
These checks use the existing field-uniform two-line code, not a sponsor RS code.
"""
import json

from probe_multiline_uniform_countermodel import FIRST_PRIME
from probe_multiline_shortening_constraints import rank


def main():
    p = FIRST_PRIME
    # Error-pencil bases for constant gamma and 2*gamma-X respectively.
    first = [(-1,-2,-3,0,0,0,0,0),(1,1,1,0,0,0,0,0)]
    second = [(0,0,0,4,5,6,0,0),(0,0,0,-1,-1,-1,0,0)]
    planes = [first,second]
    supports = [{x for x in range(8) if any(row[x] % p for row in plane)}
                for plane in planes]
    exclusive = [support-set().union(*(other for j,other in enumerate(supports) if j != i))
                 for i,support in enumerate(supports)]
    private_ranks = [rank([[row[x] for x in sorted(region)] for row in plane],p)
                     for plane,region in zip(planes,exclusive)]
    total_rank = rank(first+second,p)
    union_size = len(set().union(*supports))
    assert private_ranks == [2,2] and total_rank == 4
    assert union_size == 6 and union_size == 5+total_rank-3
    # Literal consequence for a disjoint-head cover by L three-head lines.
    n,D = 1073741824,536870913
    ambient_rank_bound = n-D+3
    minimum_cover_lines = n//3+1
    rank_deficit = 2*minimum_cover_lines-ambient_rank_bound
    deficient_lines = (rank_deficit+1)//2
    assert ambient_rank_bound == 536870914
    assert minimum_cover_lines == 357913942
    assert rank_deficit == 178956970
    assert deficient_lines == 89478485
    print(json.dumps(dict(field=p,certificate_length=8,certificate_distance=5,
                         private_region_ranks=private_ranks,total_pencil_rank=total_rank,
                         support_union_size=union_size,union_shortening_bound_sharp=True,
                         literal_length=n,literal_distance=D,
                         ambient_rank_bound=ambient_rank_bound,
                         conditional_minimum_disjoint_three_head_cover_lines=minimum_cover_lines,
                         conditional_minimum_private_rank_deficit=rank_deficit,
                         conditional_minimum_deficient_lines=deficient_lines,
                         cover_hypothesis='more than n heads partitioned into distinct three-head lines',
                         caveat='such a line cover is not proved for all canonical bad families',
                         universal_claim='sum of exclusive-region ranks <= pencil-span rank <= union size-D+3',
                         universal_claim_scope='right bound requires span rank at least three',
                         evidence='exact first-field certificate and integers, handwritten universal proof',
                         new_lean_theorem=False,threshold_improvement=False),indent=2))


if __name__ == '__main__':
    main()
