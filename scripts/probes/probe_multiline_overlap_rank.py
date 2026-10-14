"""Exact integer checks for the shared-support rank exclusion.

This checks the case ledger, not existence or completeness of code models.
"""
import json


def margins(D,t,s):
    return dict(two_rank_two=4*D-7*t-4*s,
                rank_two_and_one=5*D-11*t-3*s,
                three_rank_one=12*D-27*t-6*s,
                two_rank_one=4*D-9*t-2*s,
                exclusive_injectivity=2*(D-2*t)-s)


def main():
    checked = 0
    for D in range(1,301):
        for t in range(D):
            if not (2*D <= 5*t and 7*t < 3*D):
                continue
            overlap_floor = (4*D-9*t+1)//2
            assert overlap_floor > 0
            for s in range(overlap_floor):
                assert all(value > 0 for value in margins(D,t,s).values())
                checked += 1
    n,D,t = 1073741824,536870913,221512373
    floor = (4*D-9*t+1)//2
    assert 2*D <= 5*t and 7*t < 3*D
    assert floor == 76936148
    boundary = margins(D,t,floor-1)
    assert all(value > 0 for value in boundary.values())
    assert margins(D,t,floor)['two_rank_one'] <= 0
    print(json.dumps(dict(length=n,distance=D,error_budget=t,
                         minimum_shared_support_for_new_dependent_three_head_line=floor,
                         last_excluded_shared_support=floor-1,
                         contradiction_margins_at_last_excluded_support=boundary,
                         finite_integer_cases_checked=checked,
                         hypotheses=['2*D <= 5*t', '7*t < 3*D',
                                     'original three-head pencils have support size at least D-t',
                                     'new distinct bad three-head pencil lies in their span',
                                     'shared support is coordinates in at least two original pencils'],
                         evidence='integer case-ledger check with handwritten rank proof',
                         sharpness='not established',new_lean_theorem=False,
                         threshold_improvement=False),indent=2))


if __name__ == '__main__':
    main()
