"""Exact cube impact of disjoint three-head blocks.

The partial-spread lemma is handwritten, not kernel checked.
"""
import json

from probe_sponsor_finite_audit import N,K,P,Q,refined_degeneracy_candidate


def main():
    D,m = K+1,N+1
    assert P//Q+1 == m
    def slack(t):
        correction = 3*t*m*m+(D-t)*m
        return N*N*D*m**3+(m*(N-t))**3-N**3*m**3-N*N*correction
    lo,hi = 0,K//2
    while lo < hi:
        mid = (lo+hi+1)//2
        if slack(mid) > 0:
            lo = mid
        else:
            hi = mid-1
    assert slack(lo) > 0 and slack(lo+1) <= 0
    assert 2*lo < D and 7*lo < 3*D
    previous = refined_degeneracy_candidate()['max_error']+1
    print(json.dumps(dict(length=N,distance=D,minimum_overbudget_witnesses=m,
                         conditional_maximum_error=lo,conditional_floor_numerator=lo+1,
                         floor_denominator=N,previous_floor_numerator=previous,
                         improvement_hamming_steps=lo+1-previous,
                         strict_slack=slack(lo),next_slack=slack(lo+1),
                         ordered_collinear_triple_bound='2*m',
                         cube_deficit_bound='3*t*m^2+(D-t)*m',
                         required_structural_lemma='distinct three-head error pencils have zero intersection when 2*t<D',
                         line_cap=3,
                         evidence='conditional exact arithmetic, universal proof handwritten',
                         new_lean_theorem=False,new_production_floor=False),indent=2))


if __name__ == '__main__':
    main()
