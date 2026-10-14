"""Exact coordinate ledger for arbitrary minimal pencil dependencies."""
import json


def main():
    checked = 0
    for L in range(4,65):
        for a in range(1,L+1):
            for k in range(a+1):
                errors = 3*a-k
                nonzero_upper = 3*L*(L-1)-3*(L-a)*(L-a-1)-k*(L-a)
                exceptional = int(a == 1 and k == 1)
                assert 2*nonzero_upper <= (5*L-7)*errors+4*exceptional
                checked += 1
    n,D,t = 1073741824,536870913,221512373
    cases = []
    for L in range(4,65):
        margin = (6*L*(L-1)+4)*D-3*L*(5*L-7)*t-4*(n-L+4)
        cases.append(dict(line_count=L,necessary_inequality_margin=margin,
                          minimal_dependency_excluded=margin > 0))
    first_possible = next(case['line_count'] for case in cases if not case['minimal_dependency_excluded'])
    assert first_possible == 13
    assert all(case['minimal_dependency_excluded'] for case in cases if case['line_count'] <= 12)
    print(json.dumps(dict(length=n,distance=D,error_budget=t,
                         coordinate_cases_checked=checked,
                         first_not_excluded_minimal_dependency_size=first_possible,
                         any_twelve_three_head_pencils_independent=True,
                         necessary_inequality='(6*L*(L-1)+4)*D <= 3*L*(5*L-7)*t+4*(n-L+4)',
                         cases=cases,
                         hypotheses=['minimum distance D', '2*t<D',
                                     'distinct three-head pencils with disjoint scalar triples',
                                     'every proper subcollection independent',
                                     'shared shortening size at least D+L-4'],
                         existence_at_first_possible_size='not established',
                         evidence='exact coordinate counting and literal arithmetic, universal proof handwritten',
                         new_lean_theorem=False,threshold_improvement=False),indent=2))


if __name__ == '__main__':
    main()
