"""Audit the existing cap-three proof domain and checked upper construction.

The geometry uses existing Lean declarations. This script certifies arithmetic
and a bounded interpolation analogue, not a new production Lean theorem.
"""
from fractions import Fraction
import json

from probe_sponsor_finite_audit import construction_arithmetic,finite_interpolation


def main():
    construction = construction_arithmetic()
    n,k = construction['n'],construction['dimension']
    D = n-k+1
    current_t = 221512373
    cap_max = (3*D-1)//7
    assert cap_max == 230087534
    assert 7*cap_max < 3*D and 7*(cap_max+1) >= 3*D
    assert 7*current_t < 3*D
    upper_t = n-construction['exact_support']
    occupancy = n-construction['core']
    assert upper_t == 357913942 and occupancy == upper_t+1
    assert 3*occupancy == construction['distinct_scalars'] == n+5
    restricted_sizes = (occupancy-4,occupancy,occupancy)
    assert sum(restricted_sizes) == n+1 and min(restricted_sizes) > 3
    restricted_mass_slack = (n+1)*2**128-construction['prime']
    assert restricted_mass_slack > 0
    # Remove four scalar witnesses from line j=0, at the beginning of group 1.
    # Here height=1, so their scalar is -g^i. Source injectivity certifies
    # that no scalar in the other two families is removed.
    deleted = [(-pow(construction['generator'],joint_index,construction['prime'])) % construction['prime']
               for joint_index in range(construction['core'],construction['core']+4)]
    assert len(set(deleted)) == 4
    assert 7*upper_t >= 3*D
    joint = construction['core']
    nonjoint = n-joint
    assert occupancy*nonjoint == nonjoint+occupancy*upper_t
    pair_joint_intersection = construction['common']
    pair_nonjoint_union = n-pair_joint_intersection
    pair_nonjoint_intersection = construction['group']+construction['leftover']
    assert pair_nonjoint_union == D+1
    assert pair_nonjoint_intersection == 2*nonjoint-pair_nonjoint_union
    joint_sum_excess = 3*joint-n
    determinant_degree_upper = 2*construction['common']+1
    assert joint_sum_excess == n-5
    assert determinant_degree_upper == n-3
    toy = finite_interpolation()
    toy_line_size = toy['n']-toy['exact_support']+1
    assert toy_line_size == 44 and toy['distinct_scalars'] == 3*toy_line_size
    print(json.dumps(dict(length=n,dimension=k,minimum_distance=D,
                         current_excluded_error=current_t,
                         existing_cap_three_theorem_max_error=cap_max,
                         existing_cap_three_theorem_radius=str(Fraction(cap_max,n)),
                         domain_condition='7*t < 3*D',
                         no_claim_of_an_absolute_cap_three_radius_ceiling=True,
                         upper_error=upper_t,upper_radius=construction['radius'],
                         upper_designated_line_sizes=(occupancy,)*3,
                         upper_total_scalars=construction['distinct_scalars'],
                         exact_budget_subfamily_sizes=restricted_sizes,
                         exact_budget_subfamily_scalar_count=n+1,
                         exact_budget_subfamily_mass_slack=restricted_mass_slack,
                         removed_line_zero_scalars=deleted,
                         upper_satisfies_cap_three=False,
                         generic_t_plus_one_cap_attained=True,
                         upper_joint_core_size=joint,upper_private_size=1,
                         line_agreement_mass_equality=True,
                         pair_joint_intersection=pair_joint_intersection,
                         pair_nonjoint_union=pair_nonjoint_union,
                         pair_nonjoint_intersection=pair_nonjoint_intersection,
                         triple_joint_intersection=construction['common'],
                         determinant_joint_sum_excess=joint_sum_excess,
                         determinant_degree_upper=determinant_degree_upper,
                         determinant_criterion_margin=determinant_degree_upper-joint_sum_excess,
                         finite_interpolation_line_size=toy_line_size,
                         proof_dependencies=['IncidenceFullScaleCores.image_card',
                                             'IncidenceFullScaleCores.scalar_injective',
                                             'IncidenceFullScaleCores.exact_agreement_support',
                                             'IncidenceAffineLines.bad_witness_line_cap'],
                         evidence='existing checked construction and exact arithmetic, no new threshold'),
                     indent=2))


if __name__ == '__main__':
    main()
