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
    required_basis_nonzeros = r*dual_distance
    minimum_maximum_column_weight = (required_basis_nonzeros+n-1)//n
    assert r == n-k-2 and r > 0
    assert required_degree_sum == 288230376151711743
    assert available_degree_sum == 2147483648
    assert required_degree_sum > available_degree_sum
    assert minimum_edges == 2**57 and n == 2**30
    assert required_basis_nonzeros == 288230375614840830
    assert minimum_maximum_column_weight == 268435456
    # In systematic form [I_r | A], each row contributes one pivot entry.
    # Dual distance k+1 forces at least k entries among k+2 columns of A.
    systematic_columns = n-r
    systematic_minimum_nonzeros = r*k
    systematic_maximum_zeros = 2*r
    systematic_heavy_column = (systematic_minimum_nonzeros+systematic_columns-1)//systematic_columns
    assert systematic_columns == k+2
    assert systematic_heavy_column == 536870909
    assert systematic_maximum_zeros == 1073741820
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
    # This sends the explicit quotient certificate's three projected column
    # classes (1,0),(1,1),(1,2) to scaled incidence columns of that triangle.
    row_transform = ((2,-2),(-2,1))
    mapped = [tuple(sum(a*b for a,b in zip(row,(1,label))) for row in row_transform)
              for label in (0,1,2)]
    assert mapped == [(2,-2),(0,-1),(-2,0)]
    assert 2*1-(-2)*(-2) == -2
    print(json.dumps(dict(length=n,code_dimension=k,
                         projected_rank=r,required_dual_distance=dual_distance,
                         minimum_nonisolated_vertices=minimum_vertices,
                         required_degree_sum=required_degree_sum,
                         available_degree_sum=available_degree_sum,
                         minimum_graphic_edge_count=minimum_edges,
                         minimum_basis_nonzero_entries=required_basis_nonzeros,
                         minimum_maximum_column_weight=minimum_maximum_column_weight,
                         systematic_nonpivot_columns=systematic_columns,
                         systematic_minimum_nonzero_entries=systematic_minimum_nonzeros,
                         systematic_maximum_zero_entries=systematic_maximum_zeros,
                         systematic_minimum_maximum_column_weight=systematic_heavy_column,
                         systematic_maximum_zeros_per_row=2,
                         sparse_basis_inequality='r*(k+1) <= s*n for maximum column weight s',
                         ordinary_graphic_projection_possible=False,
                         necessary_inequality='(n-k-1)*(k+1) <= 2*n',
                         rate_half_maximum_graphic_length=8,
                         boundary_graph_edges=edges,boundary_graph_minimum_cut=min(cuts),
                         boundary_quotient_row_transform=row_transform,
                         boundary_scaled_incidence_classes=mapped,
                         hypotheses=['code dimension k and distance n-k+1',
                                     'received rows independent modulo code',
                                     'projected matrix row-equivalent to oriented incidence with nonzero column scaling'],
                         evidence='handwritten dual-distance and degree proof with exact arithmetic',
                         new_lean_theorem=False,threshold_improvement=False),indent=2))


if __name__ == '__main__':
    main()
