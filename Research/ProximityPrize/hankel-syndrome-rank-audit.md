# Affine syndrome locators and the unique-decoding boundary

Evidence class: handwritten argument with exact finite tests. No Lean theorem,
new sponsor threshold, or contribution score is asserted here.

## Scope and prior result

BCIKS, *Proximity Gaps for Reed-Solomon Codes*, already proves an n/q proximity
gap below the unique-decoding radius. See the authors' report and its revisions:
https://eccc.weizmann.ac.il/report/2020/083/ . The result below is therefore not
claimed as a new radius frontier. Its exact transfer to the given-agreement-set
bad-witness predicate is stated explicitly, rather than inferred from ordinary
proximity gaps. The later BCHKS treatment distinguishes given-set and list
correlated agreement in Sections 4.2 and 4.3:
https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf .

The purpose of this audit is to identify what a syndrome-rank route actually
controls, test its stationary-root and rank-drop steps, and expose the obstruction
to using it beyond unique decoding. The earlier abstract incidence results do
not supply the missing higher-dimensional kernel statement.

## Primitive kernel degree lemma

Let M(z) be a symmetric (s+1)-square matrix over F[z], every entry of degree at
most one, with rank s over F(z). Choose a polynomial vector v spanning its kernel
whose entries have gcd one. Then

    2 max_i deg(v_i) <= s.

Proof. Let A=adj(M). It is nonzero, symmetric, of rank one, and every column lies
in the kernel of M. Choose polynomials b_i with sum b_i v_i=1. Since column j is
a rational multiple of v, its multiplier equals lambda_j=sum b_i A_ij and is a
polynomial. Symmetry gives v_i lambda_j=v_j lambda_i. Multiplying by b_i and
summing yields lambda_j=v_j f for the polynomial f=sum b_i lambda_i. Thus
A=f v v^T, with f nonzero. If v_i has maximal degree d, the nonzero diagonal
cofactor A_ii=f v_i^2 has degree deg(f)+2d and degree at most s. This proves the
claim over an arbitrary field, including characteristic two. No division by two
inside the field occurs.

## Proposed given-set consequence

Let C be the evaluation RS code of length n and dimension k on distinct nodes.
Put r=n-k and assume 2t+1<=r. For a received line u(z)=u0+z u1, suppose m>=n+1
distinct parameters z have code heads w_z and agreement sets T_z with
|T_z|>=n-t. Suppose also that no pair c0,c1 in C agrees respectively with u0,u1
on any one of these T_z. The following handwritten argument gives a contradiction.

Use nonzero dual RS weights to write the r parity syndromes as moments s_j(z),
0<=j<r. Each s_j is affine in z. At a selected parameter, s_j is the moment of
the actual error u(z)-w_z. For actual error weight w<=t, the (t+1)-square Hankel
matrix H=(s_(a+b)) has rank w. Indeed H=V diag(error weights) V^T, and the
rectangular Vandermonde V has full column rank, while V^T has full row rank.

The determinant of H has degree at most t+1 and vanishes at all m parameters.
It is identically zero. Let rho<=t be the rank over F(z). A nonzero rho-minor
has degree at most rho. Since m>rho, some selected parameter has rank rho.
At that parameter, the leading rho-square block is an invertible square
Vandermonde factorization. Consequently its determinant delta is a nonzero
polynomial of degree at most rho.

If rho=0, all selected errors have weight zero. Two distinct selected parameters
then give u0,u1 in C, contradicting the assumed absence of a joint explanation.
Assume rho>0 below.

Let E(z,X) be the primitive kernel polynomial of the leading (rho+1)-square
Hankel block. Its X degree is rho, because the leading rho-square minor is
nonzero. Primitiveness ensures that E(z,X) is nonzero after every scalar
specialization. At every selected parameter the actual error weight is at most
rho, and Vandermonde factorization of this smaller block implies that E vanishes
at every actual error node. Away the roots of delta, there are exactly rho such
nodes. Thus E has degree rho and exactly these distinct roots there.

Let S be the set of evaluation nodes a for which E(z,a) is identically zero.
Write h=|S|, g(X)=product_(a in S)(X-a), and E=g E'. Monic division by the fixed
polynomial g shows E' is polynomial in z and X. Its coefficient vector remains
primitive, since any common divisor would also divide every coefficient of E.
Set R=rho-h.

Filter the syndromes by g, setting s'_j=sum_a g_a s_(j+a). These remain affine.
The kernel equation for E shows that E' lies in the kernel of the leading
(R+1)-square filtered Hankel matrix. All required original moments have index
at most 2R+h<=2rho. At any selected parameter away delta, filtering removes
exactly the h stationary error nodes and leaves R nonzero weighted nodes.
Therefore the filtered pencil has generic rank exactly R.

If R>0, the primitive kernel degree lemma gives 2d<=R for d=deg_z(E'). Each node
outside S is a root of E'(z,a) at at most d scalar values, since this polynomial
is nonzero. At least m-rho selected parameters have R such distinct roots.
Double counting gives

    (m-rho)R <= (n-h)d <= (n-h)R/2
    m <= rho+(n-h)/2 <= t+n/2 < n+1.

This contradicts m>=n+1.

If R=0, E is a constant nonzero multiple of g by primitiveness. Every selected
error is supported on S, with h=rho<=t. Two selected heads determine an affine
code line c0+z c1 agreeing with the received line outside S. Every other head
differs from that affine code line only on S. Since |S|<=t<r+1, code distance
forces that head to lie on the same affine code line. The assumed failure of
joint explanation on T_z therefore supplies a node in T_z intersect S where
(u0-c0,u1-c1) is nonzero. Such a node satisfies
(u0-c0)(a)+z(u1-c1)(a)=0 for at most one z. Assigning one such node to each
parameter is injective and yields m<=h<=t, again a contradiction.

This proof still requires independent mathematical audit and formalization.
Its exact first-sponsor moment window ends at t=268435455, because r=536870912.
It does not prove a new public radius frontier or the canonical Lean threshold.

## Higher-dimensional kernel obstruction

For a candidate error budget t beyond this window, r syndrome moments define
a rectangular locator system with r-t rows and t+1 columns. Even at full row
rank its kernel dimension is at least

    (t+1)-(r-t) = 2t+1-r.

The one-dimensional kernel and rank-one adjugate arguments no longer apply.
Each selected error locator can occupy a different direction in this space.
A bound on one chosen primitive vector therefore cannot count all selected
parameters. At n=1073741824, r=536870912 and t=357913941, this lower bound is
178956971. At t=268435456 it is already one, while the square symmetric matrix
used above would need one syndrome moment beyond the available r moments.

The next prize-facing requirement is a bound on the many split locators inside
this module, coupled to the fixed evaluation domain and the original agreement
sets. Treating it as one kernel vector would discard precisely the interaction
that needs to be controlled. A primitive-vector lemma alone is insufficient.

## Reproducible finite audit

`scripts/probes/probe_hankel_syndrome_pencils.py` has two independent parts.
The exhaustive rank-two enumeration uses explicit modular polynomial arithmetic
and Euclidean gcd, independently of the earlier SymPy gcd enumeration. It
checks all 59049 affine five-moment pencils over F_3, with expected census 1377
singular pencils, 1080 nonzero leading rank-two minors, 432 moving primitive
locators, and 600 stationary roots across those cases.

The second part uses symbolic determinants over finite fields on constructed
pencils of ranks 3, 5, and 8. It verifies original and filtered kernel equations,
the diagonal cofactor factorization, actual finite-field error moments, root
containment, and deliberate coefficient cancellations at exceptional parameters.
These are matrix and syndrome fixtures, not exhaustive RS families or sponsor
instances. Hosted workflow: `.github/workflows/hankel-syndrome-audit.yml`.
