"""Degree ledger for the ordinary graphic projection obstruction.

Universal inequalities are proved in the accompanying model report.
This script checks literal arithmetic and the sharp length-eight graph.
"""
import itertools
import json

from probe_multiline_shortening_constraints import literal_dimensions


def main():
    ledger = literal_dimensions()
    n,k = ledger['length'],ledger['code_dimension']
    r = ledger['conditional_projected_rank']
    dual_distance = k+1
    minimum_vertices = r+1
    required_degree_sum = minimum_vertices*dual_distance
    available_degree_sum = 2*n
    minimum_edges = (required_degree_sum+1)//2
    assert r == n-k-2 and r > 0
    assert required_degree_sum == 288230376151711743
    assert available_degree_sum == 2147483648
    assert required_degree_sum > available_degree_sum
    assert minimum_edges == 2**57 and n == 2**30
    # At rate one half, the necessary inequality is k^2-1 <=4k.
    # It fails at k=5 and its difference increases by 2k-3 thereafter.
    assert 5**2-1-4*5 == 4
    assert all(2*value-3 > 0 for value in range(5,33))
    assert [value for value in range(3,33) if value**2-1 <= 4*value] == [3,4]
    edges = [(0,1)]*3+[(1,2)]*3+[(0,2)]*2
    cuts = []
    for size in (1,2):
        for support in itertools.combinations(range(3),size):
            vertices = set(support)
            cuts.append(sum((a in vertices) != (b in vertices) for a,b in edges))
    assert len(edges) == 8 and min(cuts) == 5
    assert len(edges)-6 == 2  # The matching K dimension is six.
    assert (2+1)*5 <= 2*len(edges)
    print(json.dumps(dict(length=n,code_dimension=k,
                         projected_rank=r,required_dual_distance=dual_distance,
                         minimum_nonisolated_vertices=minimum_vertices,
                         required_degree_sum=required_degree_sum,
                         available_degree_sum=available_degree_sum,
                         minimum_graphic_edge_count=minimum_edges,
                         ordinary_graphic_projection_possible=False,
                         necessary_inequality='(n-k-1)*(k+1) <= 2*n',
                         rate_half_maximum_graphic_length=8,
                         boundary_graph_edges=edges,boundary_graph_minimum_cut=min(cuts),
                         hypotheses=['code dimension k and distance n-k+1',
                                     'received rows independent modulo code',
                                     'projected matrix row-equivalent to oriented incidence with nonzero column scaling'],
                         evidence='handwritten dual-distance and degree proof with exact arithmetic',
                         new_lean_theorem=False,threshold_improvement=False),indent=2))


if __name__ == '__main__':
    main()
