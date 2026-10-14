"""Rank-three attaining certificate and conditional rank-descent integer ledger."""
import itertools
import json

from probe_multiline_uniform_countermodel import FIRST_PRIME
from probe_multiline_shortening_constraints import rank


def certificate(p):
    u0,u1 = (-1,-2,-3,1,1),(1,1,1,0,0)
    generator = (3,2,1,1,1)
    errors = []
    for gamma in (1,2,3,4):
        coefficient = int(gamma == 4)
        error = tuple((a+gamma*b-coefficient*c) % p
                      for a,b,c in zip(u0,u1,generator))
        assert sum(value != 0 for value in error) == 2
        support = [x for x,value in enumerate(error) if not value]
        # A one-dimensional code has one coefficient per explaining row.
        explaining0 = [a for a in range(p) if all(a*generator[x] % p == u0[x] % p for x in support)]
        explaining1 = [a for a in range(p) if all(a*generator[x] % p == u1[x] % p for x in support)]
        assert not (explaining0 and explaining1)
        errors.append(error)
    assert rank(errors,p) == 3
    assert all(value % p for value in generator)
    return dict(field=p,length=5,code_dimension=1,distance=5,error_budget=2,
                bad_scalars=[1,2,3,4],error_span_rank=3,
                errors=errors,no_joint_explanation_checked=True)


def main():
    # Exhaustive explaining coefficients here deliberately use the small field.
    small = certificate(17)
    # Over the first field the same nonjointness is independently a rank test.
    u0,u1,generator = (-1,-2,-3,1,1),(1,1,1,0,0),(3,2,1,1,1)
    for gamma in (1,2,3,4):
        e = [a+gamma*b-int(gamma == 4)*c for a,b,c in zip(u0,u1,generator)]
        S = [x for x,value in enumerate(e) if value == 0]
        base = [[generator[x] for x in S]]
        assert any(rank(base+[[row[x] for x in S]],FIRST_PRIME) > 1 for row in (u0,u1))
    n,D,t = 1073741824,536870913,221512373
    target = n+1
    bounds = {1:1,2:3,3:4}
    R = 3
    while bounds[R] < target:
        R += 1
        minimum_support = D+R-3
        bounds[R] = bounds[R-1]*minimum_support//(minimum_support-t)
    assert bounds[R-1] < target <= bounds[R]
    print(json.dumps(dict(rank_three_attaining_certificate=small,
                         first_field_nonjoint_rank_checks=True,
                         literal_length=n,distance=D,error_budget=t,
                         least_overbudget_size=target,
                         conditional_minimum_overbudget_error_span_rank=R,
                         rank_cardinality_bounds=bounds,
                         recurrence='B_r=floor(B_(r-1)*(D+r-3)/(D+r-3-t))',
                         hypotheses=['independent received quotient', 'line cap three',
                                     'minimum code distance D', '2*t<D',
                                     'canonical outside-witness support bound for rank-three case'],
                         evidence='exact certificate and conditional handwritten rank-descent proof',
                         new_lean_theorem=False,threshold_improvement=False),indent=2))


if __name__ == '__main__':
    main()
