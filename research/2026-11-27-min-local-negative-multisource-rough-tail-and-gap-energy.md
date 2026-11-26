# Negative MIN: multi-source rough tail sieve and bounded-gain gaps

2026-11-27 JST. Continuation of 9314cd551bdcbd9ff5206dbb9c1e4e9876794d92.
Replace the common constant-ratio prime band in the terminal-tail sieve
by a broad polynomial range, using the extra roughness at slow
firing sources. Allow arbitrary histories inside bounded-gain gaps
and derive the corresponding restricted energy estimate.
The long-path remainder, unconditional successful-mass lower bound,
and unrestricted bad-basin energy estimate remain open. Paper-level
deductions using the same standard upper-sieve inputs as the earlier
notes; no Lean verification or claim of literature priority.

## 1. Set-up and marked suffixes

Keep the canonical roots A in [R,2R], 6|A, initial
height 3, first post-tick height H=4 floor(sqrt(R)/
(log R)^B) and gain budget L=floor(H/4), B>0 fixed.
All positions of successful roots are in [R-L,2R].
A successful endpoint a has both neighbors K-rough,
for K=c sqrt(R)/(log R)^B and a sufficiently small
fixed c>0, by the mod-30 last-idle bound of d9f6049.
The non-twin exception has one composite neighbor
a+e=q r, e in {-1,1}, q<=r prime, K<q<=sqrt(2R+1).

Fix integer k>=1 and constants 0<theta<phi with
k phi<1/2. Fix a nonnegative gap gain limit D,
with D<= (log R)^eta for some fixed eta>=0
(a fixed D is the principal case).
Select a suffix with k marked events, in reverse
order p_1,...,p_k in [R^theta,R^phi].
Between the marks and between the last mark and
the endpoint, allow arbitrary unmarked histories,
whose FULL gains d_i are even and <=D.
The suffix begins at the source of the earliest
marked event. We need not enumerate the unmarked
labels or their clocks. A natural selection is the
last k events with p>=R^theta, when their intervening
gains satisfy the cap. But the upper bound below
does not need this selection rule.

As in 9314cd5 define

    s_i = sum_(j<=i) d_j + sum_(j<i)(p_j-1),
    t_i = s_i + p_i-1.

The i-th marked event in reverse order has raw
arrival a+s_i, source b_i=a+t_i, and

    a+s_i = c_i mod p_i, c_i in {0,2}.          (1)

The suffix start is b=a+t_k.
Let a marked event be slow if w_i>=p_i/4.
Since every eligible neighbor prime has an
opportunity within twice that prime, every slow
source b_i has both neighbor least factors
>=p_i/8. We will count words with at least s
slow marks, where 0<=s<=k. To do so select
s slow indices; the finitely many choices
can be summed. A word here is the list of
(p_i,d_i,c_i) and selected slow indices, not
a full trajectory nor an arrival-time list.
Repeated p_i are allowed.

The marked source offsets t_i are strictly
increasing with t_1>=p_1-1 and
t_(i+1)-t_i=d_(i+1)+p_(i+1)-1>=R^theta-1.
Consequently the 2(s+1) shifts

    -1,1 and t_i-1,t_i+1 (selected slow i)

are all distinct for large R. Their values
are polynomially bounded in R (indeed the
actual positions lie in the original slab).

## 2. Simultaneous sieve at the endpoint and slow sources

Fix q,e and a compatible word. Let P be the
product of distinct marked labels. The congruences
(1) put a in one class mod P. Since R^phi=o(K),
q is coprime to P, so substituting a=q r-e
puts r in a single class modulo P. Parametrize
r=r0+P v. The interval for v has length O(X),
where

    X=R/(q P) >> R^delta

for some fixed delta>0, because P<=R^(k phi)
and q<=sqrt(2R+1). All potential solutions
must avoid small prime factors in the linear
forms

    q(r0+P v)-e+c,   c in the shift list.

For c=e the expression is q r; q itself
is outside the sifting range, so there is
no exception from its fixed divisibility.
For every marked slow source its two forms
are rough at cutoff >=R^theta/8; the two
endpoint forms are K-rough.

Put m=2(s+1). Choose a fixed small xi>0
depending on theta,delta,m, and sieve up
to z=R^xi, below all these roughness cutoffs,
below q, and below every marked label.
Exclude primes <=2m and primes dividing

    Delta = product_(i<j) |c_i-c_j|

where the product is over the distinct
shifts (not the arrival-side symbols of (1)).
Delta is nonzero and bounded by R^O_k(1).
For every remaining prime the coefficient
qP is invertible and the m zero classes
are distinct. The local forbidden count
is exactly m. At excluded primes we impose
no condition, valid for an upper bound.

The sieve product is

    V(z) = product_(ell<=z, good) (1-m/ell)
          <<_m (loglog R)^m/(log R)^m.

To verify uniformity: the complete product
over ell>2m is O_m((log z)^(-m)) by Mertens.
Among excluded divisors of Delta up to log R,
the reciprocal sum is at most logloglog R+O(1).
Above log R it is O_k(1) by the polynomial
bound on Delta (even the bound on the total
number of its prime factors suffices). The
inverse product over excluded primes therefore
costs at most O_k((loglog R)^m).
The dimension-m upper-sieve product condition
is uniform because omitting primes can only
decrease the product of inverse local factors
over each interval. Apply the standard
fixed-dimension upper sieve/fundamental lemma
used in earlier notes at level floor(sqrt X);
take xi sufficiently small for a bounded
upper main-term multiplier. For squarefree
d composed of good primes, the CRT remainder
is at most m^omega(d). Its sum up to sqrt X
is O_m(sqrt X log^(m-1) X), using the
elementary divisor-product bound as in 2021e5a.
This is absorbed into X V's stated upper
bound since X is polynomially large.
Consequently the count for fixed q,e,word is

    << R/(q P) * (loglog R)^m/(log R)^m.        (2)

This argument uses the standard upper sieve
already invoked in d9f6049 and 9314cd5;
no lower sieve near sqrt R and no assumption
of independence of actual histories is used.

## 3. Sum over broad bands, including repeated primes

For a fixed equality pattern on the k labels,
sum 1/P over its distinct prime values in
[R^theta,R^phi]. This is bounded by a constant
depending on theta,phi,k, because the prime
reciprocal sum in a fixed polynomial band is
O_{theta,phi}(1) (Chebyshev via dyadic intervals
suffices). Sum over the finitely many equality
patterns; compatibility constraints only
decrease the result. No repeated-label
congruence estimate is needed for this
broad-band upper bound.

Let M=floor(D/2)+1. There are at most M^k
gap choices, 2^k direction choices and
binom(k,s) slow-index choices. The composite
factor q reciprocal sum over
K<q<=sqrt(2R+1) is O_B(loglog R/log R),
as proved by dyadic subdivision in d9f6049.
Summing (2), the number E of compatible
non-twin endpoint / marked-word pairs is

    E << M^k R (loglog R)^(2s+3)
                       / (log R)^(2s+3).      (3)

Here compatible can mean satisfying only
the stated spatial divisibility and roughness
requirements, not exact clocks; actual
successful suffixes are a subset.
The result allows arbitrary unmarked event
counts in the gaps. It counts word pairs,
not root incidences. For fixed D, each
additional slow source provides two powers
of log R in the denominator, with a
loglog-factor loss.

For the common constant-ratio band [Y,2Y),
Y=R^theta, one may combine this with the
repeated-mark argument of 9314cd5 to gain
another log^(-k) factor:

    E << M^k R (loglog R)^(2s+3)
                       / (log R)^(2s+3+k).    (4)

Indeed distinct labels give this reciprocal
sum by Chebyshev. For a fixed repeated
pattern, adjacent equal marks would imply
-1+d_i in {-2,0,2} mod p, impossible by
parity when D=o(Y). Between two consecutive
occurrences of p there is a different
label r. Subtract (1) to obtain
m0 r+C=0 mod p, 1<=m0<=k<p; fixing all
other labels gives O(1) choices of r in
the common band. Thus the sum of 1/P
over assignments of a pattern with ell<k
distinct labels is O(1/(Y log^(ell-1) R)),
negligible compared with log^(-k) R.
This reasoning is uniform in each fixed
gap vector, even if D is polylogarithmic.
No extra log^(-k) claim for broad bands.

## 4. Transfer through a bipartite suffix relation

Treat the compatible pairs as edges (with word
multiplicity) between suffix starts b and final
positions a. Its maximum degrees at either end
are bounded by

    Delta_a, Delta_b <<_(k,theta) M^k.          (5)

To see this backward, fix a, choose d_1 and
one of the O_theta(1) prime divisors >=R^theta
of a+d_1 or a+d_1-2 (then the direction).
Iterate. Forward, fix b, choose a marked
label from b+/-1, then a gap d_k, iterate.
The slow-index subset flag only adds a fixed
factor. The count uses only spatial pairs,
so there is no dependence on possible
arrival times. It also allows different
word edges between the same a and b.

Restrict the prefix before b to at most d
ordinary spatial jumps or at most d macro
steps for a fixed low alphabet, as in
83647a1. Let F_d(b) be its walk majorant.
For each word edge, the number of possible
prefix roots is <=F_d(b), since distinct
roots have distinct starting vertices.
If a root has multiple admissible suffix
selections, summing all of them is still
an upper bound; the actual basin mass
counts that root only once.

Write t>=2 for a fixed Holder exponent.
Then

    N_bad <= sum_edges F_d(b)
          <= E^(1-1/t) (Delta_b sum_b F_d(b)^t)^(1/t),

    C_bad <= Delta_a sum_edges F_d(b)^2
          <= Delta_a E^(1-2/t)
                     (Delta_b sum_b F_d(b)^t)^(2/t).

The second inequality first uses Cauchy-Schwarz
at each endpoint, then Holder over the edge
list. By the earlier graph-moment bound,

    sum_b F_d(b)^t <= R [C(loglog R+d t)]^(dt).

Let D<=log^eta R and
d<=kappa loglog R/logloglog R, with fixed
eta,kappa>=0. Substituting (3)-(5) gives

    N_bad <= R log^(k eta + kappa
                      -(3+2s)(1-1/t)+o(1)),

    C_bad <= R log^(2k eta + 2kappa
                      -(3+2s)(1-2/t)+o(1)).

Here the notation log^v R means (log R)^v;
the factors denoted loglog powers in (3)
are absorbed in o(1). The two degree factors
and the edge-list factor are explicitly
accounted for, rather than treating all
possible words as disjoint populations.
Choose t sufficiently large and fixed.

For fixed D (eta=0), the resulting sufficient
depth coefficients for the broad-band case are

    kappa < 3+2s       => N_bad=o(R),
    kappa < (5+2s)/2   => C_bad=o(R log^2 R).

For growing gaps, subtract k eta from each
threshold. For the common-band version (4)
replace 3+2s by 3+2s+k and 5+2s by 5+2s+k.
The prefix macro graph must use a FIXED low
alphabet for these exponents; its wall-gap
factor is then absorbed in C. This is not
a claim that the entire marked suffix has
bounded event depth.

Alternatively if the prefix gain is <=J,
with no restriction on prefix event count,
replace F_d by the uniform bound
floor(J/6)+1. Directly from the edge-list
inequality,

    N_bad << E(J+1),
    C_bad << Delta_a E(J+1)^2.

This yields the same sufficient exponent
thresholds when J<=log^kappa R (with no
event-depth assumption). These results are
for a selected population, not an estimate
of the total successful basin energy.

## 5. Fast marks require previous gain

A different elementary restriction helps
classify paths outside the slow-source sieve.
At a marked event p with cumulative gain G
BEFORE that event, the arrival height at its
source is <=11+7G/4 for a standard height-3
root. The pre-firing height is >=(p-1)/2,
by the two height-factor identities, including
the small p=3 case. Hence

    w >= (p-1)/2 - 11 - 7G/4.

In particular a fast event (w<p/4) requires

    G > p/7 - 46/7,
    p < 7G+46.

Equivalently p>=368 and p>=8G force w>=p/4.
Thus a sufficiently large multiplicative
jump in accumulated gain must be slow.
A fast-only chain starting at gain G0
has after m events gain
G_m+45/7 <= 8^m (G0+45/7):
indeed G_new=G+p-1<8G+45.
If G0 is polylogarithmic and the chain
reaches a positive polynomial gain scale,
it requires Omega(log R) events.
This is a necessary complexity bound,
not a bound on the number of roots with
such chains. It does not show that a
typical successful path has enough slow
marks, or that their labels are within
the product budget in section 1.
The proof uses gain since the initial
canonical root; using gain since a
phase-6 restart changes the additive
constant and is not asserted here.

## 6. Executed finite audit

Source research/min_local_negative_multisource_rough_tail_audit.mjs,
commit fd1eedbb71f10474e9720dd0818a98a1a4a16fae,
blob 619463befb9e7253e3b1bcc79ee127da8c7f1850.
Executed in ECMAScript research runtime,
fetched at the exact commit and re-executed
with identical output. Reproduce with node.
No separate Node or Lean invocation.

Same six slabs and gain budgets as 9314cd5.
First enumerate all canonical successes.
Broad finite bands [7,32), [11,64), [17,128),
[31,256), with 1..4 terminal marks outside
{3,5}; classify slow marks by w>=p/4.
Check actual arrival residues, roughness at
slow sources, separation of shifts, repeated
labels, fixed-progression CRT substitutions,
local residue counts including degeneracies,
and finite interval remainders. Independently
extend the finite test to arbitrary lower-label
gaps capped at D=16 or 64, selecting the
last k events >=Y and restricting these marks
to [Y,8Y), for Y=11,17,31,47 and k=1,2,3.
Check both endpoint and suffix-start relation
degrees. All counts below refer to overlapping
finite controls, not asymptotically disjoint
populations. The actual bands are small finite
bands, not polynomial-scale statistical tests.

    roots                               289172
    completed events                   2541188
    successes                           100550
    bad successes                         7593
    slow event checks                  2256168
    broad-band controls                     96
    broad-band tail incidences          301114
    bad broad-band tail incidences       22934
    slow source checks                  390868
    separated shift checks              513306
    arrival congruence checks           992264
    repeated-mark incidences             24701
    CRT progression checks               10000
    nondegenerate residue checks         59545
    degenerate residue checks            26746
    CRT remainder checks                 86291
    generalized gap controls               144
    generalized gap incidences          573105
    bad generalized gap incidences       42734
    generalized gap shift checks       1409377
    relation degree checks              217114
    fast previous-gain checks           285020
    p>=368 and p>=8G incidences              0

All assertions passed. The last condition
was vacuous in the finite slabs, as the gain
budget is too small for p>=368; its implication
is an algebraic deduction above. The
per-event lower bound on w was checked across
all completed events. The finite CRT remainder
checks do not test the asymptotic upper-sieve
constant.

Example R=1000000, Y=17, [17,136), generalized
gaps D=16 or 64:

    D   k   successful roots   bad roots   all-slow successes   all-slow bad
    16  1          28936          2089          21916              1591
    16  2          12449           782           6979               401
    16  3           4943           288           1984                79
    64  1          37980          2781          28577              2078
    64  2          22441          1614          12088               794
    64  3          12359           827           4633               263

The all-slow condition need not be rare at
finite scales, but selecting more terminal
marks decreases the covered population.
For the last non-{3,5} event without a
band requirement, the R=1000000 control
has 37937 slow, 12103 fast, and 10551
with no such event (total 60591).
Among the 4425 bad successes, these
counts are respectively 2899,778,748.
These are finite observations, not
asymptotic mass lower bounds.

## 7. Status

The multi-source sieve yields two additional
log powers (up to loglog factors) per slow
marked source even in broad polynomial bands
and allows repeated labels and arbitrary
bounded-gain intervening paths. It extends
the depth/gain range of the selected bad-basin
estimate. The remaining problem is a theorem
covering the successful population by these
classes with sufficient mass, or an estimate
of the complement with fast chains, large
gaps or a product of labels too large for
the finite-slab sieve. Neither unrestricted
C_bad=O(R log^2 R) nor N_success>>R
is established. No proof of twin infinitude,
Lean verification, or canonical Lean target
or sibling branch changes.
