# A characteristic-eleven obstruction below one third

Evidence class: exact finite arithmetic, independently checked by polynomial
interpolation and dual annihilators. This is not a Lean result or a counterexample
to the first sponsor instance.

## The statement being tested

A tempting extension of the one-locator argument would bound the number of bad
parameters by n for all rate-half RS codes at every t<n/3, perhaps after requiring
the field to be sufficiently large. The following certificate refutes that
field-uniform extension, even on a full multiplicative subgroup. It does not
refute a theorem requiring a large prime characteristic or the sponsor's dyadic
evaluation domain.

Take F=F_11, D=F_11 minus zero, n=10, k=5 and t=3. The code consists of evaluations
of polynomials of degree less than five. In the node order 1,...,10, set

    u0 = [3,4,8,7,5,6,2,0,4,4]
    u1 = [7,7,5,8,6,2,6,7,6,10].

For every z in F_11, the fixture gives a degree-at-most-four head p_z and an
agreement set T_z of size at least seven satisfying

    u0(x)+z*u1(x)=p_z(x) for x in T_z.

On each T_z, at least one of u0 and u1 fails to extend to a codeword. Thus all
eleven distinct parameters are bad for the original given-agreement-set
predicate, and 11>n while t/n=3/10<1/3.

The complete words, heads and agreement sets are in
`../../scripts/probes/fixtures/locator-rs10-f11.json`.

## Two verification routes

`probe_locator_rank_boundary.py` enumerates all 124601 actual error patterns of
weight at most three, yielding 104001 distinct syndromes, and searches received
lines with a fixed random seed. It finds this witness at zero-based trial 95.
The selected heads are checked by interpolation on the actual domain. Failure
to find a witness would not prove absence.

`verify_locator_rs10_certificate.py` consumes the fixed fixture without using
the syndrome lookup or search. It reconstructs the polynomial coefficients of
every head and checks agreement directly. For each parameter, it also supplies
six nodes inside T_z, weights lambda_x, a row index i in {0,1}, and a nonzero
value c satisfying the exact modular identities

    sum_x lambda_x*x^j = 0 for j=0,...,4
    sum_x lambda_x*u_i(x) = c != 0.

These identities prove the absence of a joint explanation. Every polynomial
of degree less than five has weighted sum zero, while the selected received
row does not. The second verifier prints the full polynomial and dual certificate.
It also computes the ranks of the two-by-four locator matrices at all eleven
parameters, rather than inferring their ranks solely from the dimension count.

## Why a large field-size assumption is insufficient

Embed F_11 into F_(11^s) for any positive integer s and retain the same ten
evaluation nodes and received values. The eleven scalar parameters remain
distinct. Polynomial evaluation, agreements and the displayed dual identities
are preserved under this embedding. The nonzero values c remain nonzero, so
allowing coefficients in the larger field cannot repair the failed extensions.
The ten nodes still form the entire group of tenth roots of unity, since
X^10-1 has precisely those ten distinct roots already in the prime subfield.

Therefore the same bad family exists over arbitrarily large finite fields of
characteristic eleven. For any bound on field size depending only on n, choose
s large enough to exceed it. This disproves a repair using field cardinality
alone. It is a handwritten field-extension consequence of the exact identities,
not a machine-checked general field-extension theorem.

The first sponsor uses a large prime characteristic and a power-of-two domain.
Neither requirement is satisfied here. A useful new global inequality must
retain those restrictions or another condition that excludes this family.
Dropping them in pursuit of a generic rank theorem would strengthen the target
to a false statement.

## Publication scope

This fixture is a discriminating test for the active research direction.
No claim of novelty for small-field proximity-gap failures is made. It does not
establish a new production floor, a sponsor upper bound, or a SlopCash award.
