"""Feasibility of the scalar rank/shortening relaxation, not a code construction."""
import json


def main():
    n = 2**30
    k = n//2
    D = n-k+1
    t = 221512374
    L = (n+3)//3
    witnesses = 3*L
    R = k+2
    h = 2*L-R
    projection_rank_sum = 2*L
    core_rank = projection_rank_sum-h
    shared = n
    q = 3*t//2
    checks = {
        'overbudget_witness_count': witnesses > n,
        'code_dimension_bound': R <= k+2,
        'external_rank_nullity': R+h == 2*L,
        'nonnegative_relation_dimension': 0 <= h <= 2*L,
        'full_projection_core_identity': core_rank+h == projection_rank_sum,
        'rank_activity': projection_rank_sum >= h+3,
        'shared_shortening': D+projection_rank_sum <= shared+3+h,
        'three_head_support_budget': 2*q <= 3*t,
        'three_equal_root_classes': q % 3 == 0 and 2*(q//3) == t,
        'outside_witness_support_lower': q >= D-t,
        'support_inside_shared': q <= shared,
        'shared_incidence_capacity': L*q >= 2*shared,
        'pair_union_capacity': D+1 <= min(2*q,n),
        'small_error_regime': 7*t < 3*D,
        'twelve_plane_rank_capacity': R >= 24,
    }
    # The relaxed union upper bound is min(s*q,n). Its comparison with the
    # independent-subfamily shortening lower bound has only one breakpoint.
    independent_limit = R//2
    breakpoint = (n+q-1)//q
    samples = sorted({2,3,breakpoint,independent_limit})
    checks['independent_subfamily_union_capacities'] = all(
        D+2*s-3 <= min(s*q,n) for s in samples)
    assert all(checks.values()), checks
    assert shared+3+h-D-projection_rank_sum == 0
    print(json.dumps({
        'scope': 'scalar feasibility only, no support family or code is constructed',
        'length': n, 'code_dimension': k, 'distance': D, 'error_budget': t,
        'line_count': L, 'witness_count': witnesses,
        'ambient_error_rank': R, 'relation_dimension': h,
        'each_projection_rank': 2, 'relation_core_rank': core_rank,
        'shared_support_size': shared, 'each_plane_support_size': q,
        'shared_shortening_slack': 0,
        'checks': checks,
        'independent_union_capacity_sample_sizes': samples,
        'conclusion': 'these scalar constraints alone do not exclude an overbudget ledger at the current floor',
        'not_checked': ['compatible actual supports', 'linear realizability',
                        'canonical bad witnesses', 'all moment constraints',
                        'Reed-Solomon realizability'],
        'new_threshold': False,
    },indent=2))


if __name__ == '__main__':
    main()
