# Negative MIN: literature reassessment, Shannon frontier and grouped large-sieve transfer

2026-11-27 JST. Continuation of 02b231874e85a9249f1e1713bd3e7b7e36620339.
This is a strategic reassessment rather than another attempt at a
worst-case local return cap. It compares the actual remaining MIN
problem with the parity obstruction and recent two-point correlation
and shifted-prime preprints. New paper-level deductions: an entropy
effective-support sufficient criterion for twin infinitude, an exact
entropy flow identity and fresh insertion bound with no third moment,
a rare-key entropy inequality, and an aggregate grouped large-sieve
upper bound for adaptive pin sets. These do not establish the necessary
asymptotic estimates. Two reproducible audits are provided.
No Lean verification or claim of literature priority.

## 1. Literature, exact scope and relevance

Sources inspected 2026-11-27:
- Polymath, Variants of the Selberg sieve, and bounded intervals
  containing many primes, Research in the Mathematical Sciences 1:12
  (2014), Theorem 4 and Parity problem section:
  https://link.springer.com/article/10.1186/s40687-014-0012-7
  Classical bound H1<=246, conditional H1<=6 on GEH, and the
  parity obstruction for the stated purely sieve-theoretic framework.
  These are historical statements, not a claim of the latest numerical
  unconditional gap bound.
- T. Tao, A general parity problem obstruction (2014-11-21):
  https://terrytao.wordpress.com/2014/11/21/a-general-parity-problem-obstruction/
  The convex-hull formulation is explicitly informal. Chen's
  prime/almost-prime property and the two-prime property differ here.
  The obstruction is not a theorem against every possible dynamic
  construction using divisibility.
- T. Tao, Notes on the Bombieri asymptotic sieve (2016-07-17):
  https://terrytao.wordpress.com/2016/07/17/notes-on-the-bombieri-asymptotic-sieve/
  On GEH, a rough-restricted two-point Mobius cancellation at
  scale o(X/log^2 X) is a route to the Hardy-Littlewood pair asymptotic;
  ordinary Chowla is not that statement. The restriction removes the
  small prime factors used in multiplicative dilation arguments.
  A conditional alternative is a lower bound for balanced rough
  semiprime pairs p1*p2-p3*p4=2. Do not drop GEH from that reduction.
- H. A. Helfgott and M. Radziwill, Expansion, divisibility and parity:
  https://arxiv.org/abs/2103.06853
  Abstract and operator: symmetric centered divisibility graph
  with edges n to n+/-p, mean weight 1/p, norm on a density-one
  good set O(sqrt(sum 1/p)) in a subexponential prime range
  log H <= (log N)^(1/2-epsilon).
- C. Pilatte, Improved bounds for the two-point logarithmic Chowla
  conjecture: https://arxiv.org/abs/2310.19357
  Replaces prime steps by products in graph/expansion arguments.
- OpenAI, Ordinary two-point correlations of multiplicative functions,
  2026-09-24, release scope and comparator links:
  https://github.com/openai/math/blob/main/lean/docs/007.md
  The published scope note reports ordinary affine binary Liouville
  correlation O(X/(log X)^c) for fixed nonproportional forms and an
  absolute c>0, and corrected Elliott cancellation.
- G. Lu, Z. Wang, J. Wu, On the Hardy--Littlewood--Chowla conjecture,
  2026-10-14, latest viewed text dated 2026-11-20:
  https://arxiv.org/abs/2610.20242
  Abstract claims sum_(p<=X) mu(p+2)=o(pi(X)).
- J. D. Lichtman, Improved bounds for the binary Chowla conjecture,
  2026-11-20: https://arxiv.org/html/2611.28392v1
  Theorems 1.1 and 1.2 claim respectively
  O_epsilon(X/log^(1-epsilon) X) for binary Mobius
  correlation (also fixed other nonzero shifts and Liouville),
  and O_epsilon(pi(X)/log^(1/2-epsilon) X) for shifted
  prime Mobius. Sections 4-11 use typical prime-divisor patterns,
  determinant bilinear forms, exact prime interval partition and
  prime-list lifetime operators. The active primes are
  subexponential; typical-integer estimates with arbitrary
  log savings do NOT assert the same on all exceptional
  integers. In particular both fully polynomially rough
  neighbors have none of the required active prime factors.
  Proposition 7.1 and Corollary 7.4 cannot be applied as if
  their support restrictions were arbitrary rough weights.
- Standard additive large sieve, Montgomery--Vaughan:
  https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf
  Use its classical separated-frequency bound, independently
  deriving the residue-class form below.
The 2026 papers are described according to their actual statements
and scope, not independent certification of every proof. A follow-up
index linked a manuscript 'Rough numbers at a fixed distance with
prescribed Liouville signs'; its original GitHub PDF and repository
returned 404, so it is not used as an established result.
No exhaustive novelty or priority claim.

## 2. Where a proof must gain new information

For a near-square-root rough center a, both a-1 and a+1
have at most two prime factors counting multiplicity.
Write lambda=(-1)^Omega. Their simultaneous primality
indicator is EXACTLY

    1_tw(a)=(1-lambda(a-1))(1-lambda(a+1))/4.

For nonnegative weight W supported on these centers,
the sufficient signed inequality is

    sum W(1-lambda_- -lambda_+ +lambda_- lambda_+)>0.

Even sum W(lambda_-+lambda_+)<0 suffices. Ordinary
Chowla or shifted-prime cancellation over all integers
is much too weak to substitute in this sparse sum.
Another direct literature-based target is a positive
Chen weight supported on prime/at-most-two-prime-factor
pairs, of mass >>X/log^2 X, with signed Mobius sum
o(X/log^2 X). Squares need to be removed or bounded;
then a negative sign distinguishes the prime side.
Existing shifted-prime results do not give that
restricted signed bound. This is an explicit alternative,
not a derivation of twins from Chen and ordinary Chowla.

MIN's exact raw divisibility edge is, for sign sigma,
a -> a-p+1 with p | a-sigma. Set x=a-sigma.
The spatial centered raw operator has the form

    A_sigma f(x)=sum_(p in P)(1_(p|x)-1/p)
                                      f(x-p+sigma+1).

It is a translated directed half of the kind of
divisibility graph studied by Helfgott--Radziwill.
Trace moments of A A* produce alternating closed
prime words; fresh/repeated prime constraints match
the earlier MIN relay/prime lifetime combinatorics.
But the physical winner has a clock and priority
mask, the graph is directed, and the mass depends
on its past. The symmetric static operator norm
cannot simply be quoted for this masked operator.
Its prime range also does not reach sqrt R.
A density-one exceptional-set result alone is
inadequate for a cohort supported on O(R/log^2 R)
rough centers. A promising import is a trace bound
for the clock-masked *centered* transition or a
bilinear bound with the root-history weight.
This could supply a new type of estimate, rather
than more finite worst-case local maxima.

## 3. Shannon effective support at the rough frontier

Use the already derived square-root horizon and rough
frontier lemma (d9f6049). For fixed B>0 put
K=floor(sqrt(R)/(log R)^B), T=4K. For canonical roots
A in [R,2R], 6|A, G_T<=gT with fixed g<2/9 gives
I_T >= T-9G_T/4-8>2K for sufficiently large R.
Its endpoint a=A-G_T is K-rough on both sides.
It lies in [R-O(sqrt R),2R]. Non-twin rough centers
in this range number at most

    B_R <<_B R loglog R / log^3 R,

by the fixed-q two-dimensional upper sieve of d9f6049:
a composite neighbor is qr with K<q<=sqrt(2R+1),
r prime; the other neighbor qr+/-2 is K-rough.
The sum over q in the narrow near-sqrt band supplies
the extra reciprocal-prime logarithmic saving.

Let S be ANY selected nonempty cohort with this
low gain condition, N_s=|S|, m(a) its endpoint
multiplicity. Let A be uniform on S and P(a)=m(a)/N_s.
Define entropy loss

    L_s=H(A|a_T)=(1/N_s) sum_a m(a) log m(a).

This is log N_s minus Shannon entropy of a_T.
The effective support satisfies

    D_s >= N_s exp(-L_s)
           >= N_s^2 / sum m(a)^2.              (1)

First inequality: Shannon entropy <= log support.
Second: Jensen, E_S log m<=log E_S m.
Under absence of twins in the endpoint range,

    L_s >= log(N_s/B_R).                      (2)

Thus if s_R=N_s/N_R is the selected root fraction,
a single sufficient scalar condition on unbounded slabs is

    s_R exp(-L_s) >> loglog R/log^3 R          (3)

where >> in (3) means the ratio tends to infinity
(or an explicit larger constant than the bad-count bound).
In particular if s_R >= c (log R)^(-gamma) and

    L_s <= (3-gamma-delta) loglog R             (4)

for fixed delta>0, twin infinitude follows. This is
strictly weaker than requiring a corresponding bound
on the normalized second moment. Large rare merger
masses are only logarithmically charged. It also
requires a lower bound on the selected population,
NOT a saving in the mean gain of the whole cohort.

There is a quantitative consequence. Write t for
the fraction of selected roots with twin endpoints,
and let P_R be the number of twin centers in the
endpoint range. The entropy chain rule for the
two types gives

    log N_s - L_s <= h_2(t)+(1-t)log B_R+t log P_R.

When a type is empty omit its term. With the standard
upper sieve P_R<<R/log^2 R, (4) implies t>=delta-o(1).
In particular if s_R is bounded below, entropy loss
at most (2+o(1))loglog R would force almost all
selected roots to be at twin endpoints. This is
a sufficient criterion with upper sieve input,
not a claimed lower bound for t at growing R.

## 4. Why entropy loss might be a natural scale

On a complete finite canonical period of restricted
absorption through cutoff y, the absorber is a
multiple of six. Put M=2 product_(5<=p<=y) p,
V=product_(5<=p<=y)(1-2/p).
There are exactly MV rough canonical residues in
this period. Uniform initial j=A/6 gives some
output distribution P on these residues; U is
uniform rough distribution. The exact identity is

    L_y = log(1/V) + D_KL(P||U)
        = 2 loglog y + O(1) + D_KL(P||U).       (5)

Moreover since U is a product over prime coordinates
(and half-distance parity),

    D_KL(P||U) =
        sum_i D_KL(P_i||U_i)
         + [sum_i H(P_i)-H(P)].

The last term is total correlation of the endpoint
coordinates. The 2 loglog y term is the unavoidable
loss merely from two forbidden classes per prime;
only marginal bias and cross-prime correlations
need extra control. If the excess relative entropy
is small, mass is not concentrated into the rare
rough endpoint subfamilies. There is no proof that
it is small at growing y, and (5) is for the complete
formal period, not an actual near-sqrt slab.

For an arbitrary event set E and reference U with
U(E)=q, data processing gives
D_KL(P||U)>=P(E) log(1/q)-log 2.
Hence D_KL=o(loglog R) would imply P(E)=o(1)
when q<=log^(-delta) R, delta>0. This suggests
an entropy rather than maximum-fiber treatment
of bad endpoint concentration. To use this in actual
slabs a suitable reference measure and transfer
must be established, not inferred from (5).

## 5. Exact entropy transport and fresh insertion

In a record-return forest (f8b2421), u_b(a) is
first-cut mass, v_b(a) total traffic. At a vertex
v=u+sum_(x->a) v(x). Put f(t)=t log t, f(0)=0.
For a fixed common root set N define
L_b=(1/N)sum u_b log u_b. Exact cancellation
of all internal edge terms yields

    N(L_(b+1)-L_b) =
      sum_a [f(v_b(a))-f(u_b(a))
                               -sum_(x->a) f(v_b(x))].  (6)

Each bracket is v times the Shannon entropy of
the incoming branch identity, counting the base
cohort as another incoming option. All are
nonnegative. No maximum branching or third
moment is required for the exact ledger.

For a fresh prime p=2b+1 at record level b, use
the complete renewal map of e40e4c5, old exit
mass U, old period M, enlarged period pM.
Let X be activated positive-mass source lifts,
A0=sum_X U(x), alpha=A0/(pM)<=1/p.
For final lifted target y, let I(y) be incoming
mass of activated cohorts, B0=sum_(I(y)>0) U(y mod L).
The entropy increment is exactly cross mixing
plus internal mixing:

    pM Delta L =
       sum_y [f(U+I)-f(U)-f(I)]
          + [sum_y f(I)-sum_X f(U(x))].         (7)

The first term is bounded above by
f(B0+A0)-f(B0)-f(A0) by concavity of binary entropy
(or the log-sum inequality).

For the second term choose an activated root
uniformly. Conditional on its terminal y, its
source is determined by the nonnegative integer
k=floor(D_x/(4p)), where D_x is total displacement
including all renewal steps, 0<D_x<Lp.
Indeed activated positions are spaced by 4p
and D_x is the actual displacement of the unique
physical lift. The maximum Shannon entropy of
a nonnegative integer variable of mean d is

    g(d)=(1+d)log(1+d)-d log d, g(0)=0,

as follows by comparison with the geometric
distribution of mean d. Conditional entropy
is no greater than unconditional entropy, so
putting dbar=(sum_X U(x) floor(D_x/(4p)))/A0
we obtain

    Delta L <= alpha [g(B0/A0)+g(dbar)].        (8)

Use zero increment if A0=0. Unlike the earlier
quadratic bound, the internal term needs only
a FIRST displacement moment of activated mass;
the cross term needs the total base mass on
its terminal keys, not K3. When both ratios
are bounded, the fresh contribution is O(1/p).
Its sum over prime insertions is O(loglog y).
The coefficient, old-label transport, and actual
slab transfer still need estimates to reach (4).
For p=11,13,17,19 exact controls below have
cross ratios 1.13-1.67 and very small dbar.
No general bound on these ratios is claimed.

A related gain-weighted entropy certificate:
for nonnegative key masses m_e and capacities
w_e>0 let B=sum w_e, L=sum w_e m_e>0.
Under gain-biased distribution P_e=w_e m_e/L,

    log(L/B) <= sum_e P_e log m_e.             (9)

This is nonnegativity of KL relative to w_e/B.
For positive-credit events c=(4w-(p-1))_+,
c<=11(p-1); w>(p-1)/4 implies smallest
neighbor prime >(p-1)/8. At macroscopic
p>=c0 T with T comparable to sqrt R, the
fixed prime rough-source upper sieve and
height-local clock count give total distinct
key capacity B<<R T/log^3 R (using w_e=11(p-1)).
Take m_e=total positive credit/(11(p-1)),
possibly fractional. Then a bound on the
credit-biased mean log m_e below
(3-delta)loglog R implies E_R credit=o(T)
for this band. This replaces quadratic traffic
control by a logarithmic criterion; small and
intermediate credit still remain. This is
not an assertion that the entropy of the
final endpoint automatically controls the
credit-biased logarithm at the needed coefficient.

## 6. Aggregate transfer via large sieve, not full CRT

Consider actual j=A/6 in an interval of N
consecutive integers. Let their low-alphabet
paths (cutoff Y) define adaptive high pin sets
for p in [Y,2Y], all p>=5, converted to j residues.
Partition roots into arbitrary deterministic
descriptor classes S_tau of size n_tau.
The descriptor need not be a full trajectory,
nor a residue modulo a primorial. Suppose it
supplies supersets D_(tau,p) of every actual
pin set in that class. Put

    w_tau=sum_(Y<=p<=2Y) |D_(tau,p)|/p,
    pi_tau=n_tau/N.

For each class and prime let n_(tau,p,r) be
the count in residue r. Parseval on Z/pZ
identifies

    sum_p p sum_r (n_(tau,p,r)-n_tau/p)^2
      =sum_p sum_(a=1..p-1)
                |sum_(j in S_tau) exp(2pi i aj/p)|^2.

All reduced frequencies a/p are 1/(4Y^2)
separated on the circle, so the standard
additive large sieve bounds this by
(N+4Y^2) n_tau. Weighted Cauchy over the
superset pins gives total positive discrepancy
at most sqrt(w_tau (N+4Y^2)n_tau). Summing
and applying the deterministic union bound
from the high-alphabet deletion law,

    Pr_R(a first omitted winner in the band)
        <= sum pi_tau w_tau
         + sqrt(1+4Y^2/N) sum sqrt(pi_tau w_tau). (10)

The event means first outside the retained
alphabet and in this band, or first band
event in the gap model. The construction
does not control later band events after
other omitted labels have fired.

If all but epsilon root mass are covered
by k descriptor classes, discard the
remainder in (10), adding epsilon.
With W=sum_(retained) pi_tau w_tau,

    Pr_R <= epsilon + W + sqrt((1+4Y^2/N) k W).

In the actual sqrt range Y~sqrt N, if W=O(1/log N)
and k=o(log N), transfer follows regardless
of the size of the primorial. More generally
the weighted square-root sum in (10), not
the raw number of classes, is the target.
For a fixed low alphabet with absorption
before any high tick, grouping by its
absorption displacement gives a finite
descriptor count and two residue pins per p.
This recovers a rare-event upper bound at
square-root scale (the previous direct CRT
calculation is sharper in that fixed case).
For a growing low alphabet no descriptor
compression with the required exposure and
mass is established. This is a specific
large-sieve transfer criterion, distinct
from an assumption of full CRT independence.

## 7. Executed finite audits

A. research/min_local_negative_frontier_entropy_audit.mjs
   commit 1a05a54e95830d297dbbba0d251729c3b962d270
   blob b016386973ae344ca28b50e5f2f604995d0eecfb
All canonical roots in R=12000,48000,192000,480000,
1000000,2000000. K=floor(sqrt R/sqrt(log R)),
T=4K, J=floor(T/5). Count every rough center
in the expanded slab by exact least factors,
compute all event paths, select G_T<=J,
verify roughness and entropy inequalities.

    roots                  622004
    events               14181783
    selected rough checks  207261
    entropy checks              12

For R=2000000:
N=333333, N_s=115899 (34.77 percent),
distinct=13090, all bad rough centers=11616,
selected twin mass=105642, L_s=2.6210987424.
Shannon effective support=8428.51,
collision effective support=6501.46.
The entropy lower bound improves on collision
bound but does NOT exceed the finite bad
count in this test; distinct support does.
Thus (3) has not been numerically certified
even on these particular selected populations
by this sufficient entropy inequality.
The finite actual mean gain ratio=.59097,
so the weaker selected-population route is
motivated independently of an all-root
mean-gain saving. No asymptotic conclusion.

B. research/min_local_negative_fresh_prime_entropy_audit.mjs
   commit d6c924908c41d49f17a3b5306e1e6f7ea41d9244
   blob 317657d524b79cc87311a81ef496b9240ffe148c
Extends exact renewal audit of e40e4c5
for p=11,13,17,19, all old phases,
independent full lifted periods through p=17
and deterministic sample at p=19.
Computes (7),(8), compares direct entropy.

    old roots              181020
    activated nodes        271530
    direct lifted checks   214283
    energy checks          542854
    entropy checks              7

    p    actual Delta L    upper (8)    base ratio    dbar
    11       .077284        .081567       1.16667      0
    13       .052781        .056557       1.26648      0
    17       .053546        .056981       1.67305      0
    19       .032947        .037881       1.12903      .000506

Both scripts were executed, fetched at the exact
commits and re-executed with matching output.
No Node or Lean invocation outside the research
ECMAScript runtime. The exact (6),(9),(10) are
paper deductions, not separate numerical audits.

## 8. Research priority

Do not continue searching for the false sublogarithmic
worst-case return cap. First try to establish on
actual near-square-root slabs a nontrivial low-gain
selected mass and entropy loss below the threshold
(4), using (6) and (8) as a transport entropy ledger.
This directly reaches the bad-frontier contradiction
without proving the entire mean gain bound, a uniform
second moment, or controlling post-cut histories.
The earlier formal CRT transfer gap is still essential.
Use (10) to test compression of first-omitted pin sets;
use literature-inspired centered divisibility graph
estimates for more general masked transition weights.
The prime-conditioned rough Mobius route is a separate
parity-sensitive target, especially in view of the
November 2026 preprints; their typical-integer arguments
do not yet cover the sparse rough/prime case.

None of these new sufficient criteria is shown
asymptotically. No twin-infinitude proof or Lean
verification, no canonical target/sibling branch or
Context changes.
