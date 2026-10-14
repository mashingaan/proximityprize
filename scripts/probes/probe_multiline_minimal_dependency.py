"""Integer ledger for the minimal dependent family shortening argument.

This does not assert existence of any dependent-pencil construction.
"""
import json


def bounds(D,L,defect):
    assert L >= 4 and defect in (1,2)
    R = 2*L-defect
    union_lower = D+R-3
    shared_lower = D+L-4 if defect == 1 else union_lower
    return dict(line_count=L,rank_defect=defect,span_rank=R,
                support_union_lower=union_lower,
                shared_support_lower=shared_lower,
                all_support_shared=(defect == 2),
                total_error_incidence_lower=2*union_lower+2*shared_lower)


def main():
    D,t,n = 536870913,221512373,1073741824
    cases = [bounds(D,L,defect) for L in range(4,13) for defect in (1,2)]
    for case in cases:
        L = case['line_count']
        assert case['span_rank'] in (2*L-1,2*L-2)
        assert 3*L*t >= case['total_error_incidence_lower']
    assert cases[0]['shared_support_lower'] == 536870913
    assert cases[1]['shared_support_lower'] == 536870916
    print(json.dumps(dict(length=n,distance=D,error_budget=t,
                         minimal_dependency_cases=cases,
                         hypotheses=['each pencil has dimension two and quotient isomorphism',
                                     'every proper subcollection is a direct sum',
                                     'code minimum distance D',
                                     'three bad witnesses of error weight at most t per pencil',
                                     'at least four pencils'],
                         universal_argument='a relation spans a code shortening on the shared coordinates',
                         existence_of_dependent_family='not established',
                         evidence='integer ledger, universal proof handwritten',
                         new_lean_theorem=False,threshold_improvement=False),indent=2))


if __name__ == '__main__':
    main()
