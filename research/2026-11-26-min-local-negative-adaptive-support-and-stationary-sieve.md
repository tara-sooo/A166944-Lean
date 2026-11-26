# Negative MIN: adaptive sparse-core obstruction and finite-interval stationary-extension sieve

2026-11-26 JST. Continuation of 0116e3e87b2e3916bae3335dbbce117b0fa68f86.
Two asymptotic results: a deterministic waiting-time bound for
arbitrary sparse label cores with exceptions, and a sieve transfer
for a stationary waiting segment following a bounded-modulus
adaptive transcript. The latter gives actual canonical roots with
a specified nonempty initial event word and polynomial-length
subsequent idleness. Neither establishes a linear-scale idle
segment, nor the stopped-prefix existence theorem. Paper
arguments and executed finite audits; no Lean verification.

## 1. Robust adaptive support gap

Consider a contiguous block of ordinary completed negative-MIN
events with decreasing positive even distances, all non-twin
sources in (A/2,A], and full cumulative gain G<=A/2.
Then each wait w<=2 min(p,S), S=sqrt(A+1), and
w<=3(p-1). Allow an arbitrary finite core alphabet P of k
distinct odd primes, chosen AFTER observing the path if desired.
Let E count all events with label outside P.

For U=sqrt A>1, put r=U^(1/2^k).
Order the core primes strictly below U, and let Q_i be
the product of the first i, Q_0=1. There exists T<=U
for which the product Q of core primes strictly below T satisfies

    Q/T <= 1/r.                                   (1)

Indeed, if some next prime p>=r Q_i, take T=p at its
first such occurrence. Otherwise every multiplication
obeys Q_(i+1)<r Q_i^2, giving Q_i<=r^(2^i-1).
At T=U the product of all lower core primes is then
<=r^(2^k-1)=U/r. This includes the empty-core case.

For an arbitrary T<=U, let M_T be the maximum half-distance
gap of complete static walls for the lower core alphabet
P_<T, as defined in 0116e3e. Use M_T=1 if empty.
Always M_T<=Q. Write L_T=#(P intersect [T,infinity)).
Suppose T/M_T>=4; in particular T>=4, so marked primes
p>=T are >=5. Cut the block at every exceptional event.
In each resulting component mark core labels >=T.

Each lower-core run has full gain <2M_T; the number
of such runs is at most h+E+1 where h is the total
number of marked events. We have h<=G/(T-1).
The wait of all low-core events is thus <=6M_T(h+E+1).
Each relay between consecutive marks in one component
has even gain <2M_T<T-1. As in 755b0ce its labels
p,r must be distinct. For fixed p,r,e,f and relay gain,
the first source is in one class mod 2pr. All
such sources across all components remain distinct.
Write D=A/2+1 for a containing integer interval length.
Their count is <=D/(2pr)+1; their wait sum is
<=D/r+2S. There are at most M_T even relay gains,
four sign choices and L_T(L_T-1) ordered unequal
label pairs. Group across all components, not once
per component, to get

    W_pair <= 4 M_T L_T(L_T-1)(D/T+2S).

At most E+1 last marks are left, each costing <=2S.
The exceptional events themselves cost <=2SE.
Hence the full bound is

    W <= 6M_T(G/(T-1)+E+1)
       +4M_T L_T(L_T-1)(D/T+2S)
       +2S(2E+1).                                 (2)

Using T<=sqrt A and M_T<=T/4 in (2) gives

    W << (L_T+1)^2 A M_T/T + S(E+1).               (3)

For T/M_T<4 the same estimate, with a larger absolute
constant, holds trivially by W<=3G<=3A/2. Thus (3)
holds uniformly for every 2<=T<=sqrt A; if A is too
small to have such a T use the trivial bound.
Minimize the first term over thresholds, or use (1)
and M_T<=Q. This proves the unconditional block inequality

    W << (k+1)^2 A^(1-2^(-(k+1))) + sqrt(A+1)(E+1). (4)

All implied constants are absolute and independent of the
chosen primes, k and E. For r<4 or U<2 the trivial wait
bound suffices. One can retain L_T and actual wall gaps in
(3), which can be considerably sharper than (4).
No stochastic or typical-support assumption is used.

## 2. Consequence for actual canonical non-twin prefixes

Use the stopped prefix of cc62807: start A=6j,
v=3-A/2, stop at a<=A/2 or before a firing after -1.
If half crossing occurs, omit that last crossing
event from the block. If there is no twin center
in (A/2,A], the trimmed block has G<A/2 and

    W >= A/4-O(sqrt A).

This is the finite witness argument of cc62807.
It applies even if the interval has no actual events
after trimming; in that case the lower bound rules
it out for sufficiently large A.

For fixed 0<epsilon<1, if

    k <= (1-epsilon) log_2 log A,

then (k+1)^2 exp(-log A/2^(k+1)) tends to zero.
By (4) a block with such a core and E=o(sqrt A)
has W=o(A), contradicting the non-twin lower bound.
Consequently for sufficiently large locally twin-free
canonical roots every such core must leave Omega(sqrt A)
exceptional events. The constant is uniform in the
choice of core (and the large-A threshold can depend on
epsilon). The same holds under the global finite-twins
hypothesis for all sufficiently large canonical roots.

There is a useful truncated-support version. Let F(A)
tend to infinity, and take the core to contain all distinct
labels actually used in the trimmed prefix with
p<=F(A)sqrt A. The others satisfy

    E <= G/(F(A)sqrt A-1)=o(sqrt A).

Thus locally twin-free large roots must use more than
(1-epsilon) log_2 log A distinct labels in that truncated
range, for every fixed epsilon>0. This ignores arbitrarily
large labels above the cutoff. An arbitrary finite core
of fixed cardinality, even with primes growing with A,
cannot support a macroscopic wait without many exceptions.
These are genuine uniform asymptotic obstructions for
actual trajectories, but they are NOT existence of roots
with sufficiently sparse core. They do not imply such a
core occurs infinitely often.

The all-primes wall strategy cannot be pushed to polynomial
cutoffs solely by improving maximum-gap estimates: for all
odd primes <=z, the exact wall density from 0116e3e gives

    mean gap = 2^(pi(z)-1) prod_(3<=p<=z)(1-1/p)^(-1)
             asymp 2^pi(z) log z.

The maximum is at least the mean, already superpolynomial
in A for z=A^theta, theta>0 fixed, by the prime number
theorem. Actual selected supports or phase-dependent
barriers are therefore essential if using (3) near
the square-root scale.

## 3. Adaptive addition of a large prime to the wall alphabet

Let old wall maximum gap be M, and add a prime p not
already in the alphabet, with (p-1)/2>=M.
The new condition (-J mod p)<=(p-3)/2 allows consecutive
integer runs of length L=(p-1)/2, separated by forbidden
runs of length p-L. Every allowed run contains an old
wall because its length is at least M. Within one run
old gaps remain at most M. Across two successive runs,
the last old wall in the first run and first old wall
in the second are each within M-1 of the respective
boundary. Thus the new wall maximum gap satisfies

    M_new <= p-L+1+2(M-1)=(p+1)/2+2M-1.            (5)

This bound is often much smaller than p times the old
period; it is deterministic, applies to any support, and
does not assume random wall locations. It does not give
an effective uniform recursion for primes with L<M.
The exact M_T or (5) may be substituted in (3).

## 4. Stationary extension: exact local sieve input

Return to the canonical elapsed tick representation
of 0116e3e. Let I be an interval of N consecutive j
values whose A=6j lie in a physical slab of scale R,
N comparable to R. Fix an exact finite adaptive
prefix transcript up to elapsed tick t0, including
idle ticks, and condition on one residue class

    j=b mod m,  m=2 prod_(q exposed,q>=5) q.

More generally m may include extra odd prime factors
>=5. Parity is fixed, and all roots in this class
must share the prefix. The prefix gain is G, current
height h=3+t0-G/2>=0. Assume throughout that the
physical stopping condition cannot intervene before
t0+K, for example t0+K=o(R), using G_t<=2t+6.

Ask for NO firing in the next K ticks. On that
stationary extension a=6j-G and the clock at its
start is v=3-3j+t0. A candidate q>=5 has at most
two eligible root residues, r_e=6^(-1)(G+e) mod q.
For each side e, fix the root parity and compute the
candidate's wait on this class, as in d577559.
Include r_e in a forbidden set B_q exactly when
that wait is <=K. This test is necessary and
sufficient for idleness, since while no event
occurs the spatial state remains constant.

Prime 3 is a deterministic gate. For q dividing
m the eligibility and wait are fixed; if any such
clock fires within K, the entire class is impossible.
Otherwise these primes impose no further restrictions.
For all remaining primes q not dividing m, write
j=b+m l; the forbidden set in l has nu_q=|B_q|
in {0,1,2} residues. By the height-local scan,
all such candidates have q<=z=2(h+K)+1
(or take max(5,z)). This follows by considering
the first firing if it exists, for which the
height before that tick is at most h+K.
The odd height expression has absolute value
<=2(h+K)+1. Thus the entire future idle condition
is a stationary finite sieve, not an adaptive
branching process.

For the progression parameter l in its interval
of length N_b, squarefree d supported on these
free primes has exactly nu(d)=prod_(q|d)nu_q
forbidden-intersection classes mod d, so the
intersection count is

    N_b g(d)+r_d, g(d)=nu(d)/d,
    |r_d|<=nu(d)<=2^omega(d).                      (6)

If nu_q=0 the corresponding forbidden set is
empty. The estimate is uniform in the prefix,
the modulus, and the actual positions of the
forbidden residues.

## 5. Unconditional finite-interval transfer via the fundamental lemma

Use the dimension-at-most-two fundamental lemma of
sieve theory with level D=floor(sqrt N_b), s=log D/log z
(use z+1 if needed at an endpoint). The precise
standard input is Lemma 17 and Corollary 19, equation
(22), in Terence Tao, "254A, Notes 4: Some sieve theory",
2015-01-21, verified 2026-11-26:
https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/
Its required product condition is satisfied uniformly
here since 0<=g(q)<=2/q for q>=5, g(2)=g(3)=0,
and Mertens' theorem bounds the interval product
by an absolute constant times the square of the
logarithm ratio. Omitting any primes dividing m
or using nu_q=1 only decreases that product.

Write V=prod_(5<=q<=z,q not dividing m)(1-nu_q/q).
We have V >> (log z)^(-2). By (6),
sum_(d<=D) |r_d| <= sum_(d<=D) 2^omega(d)
<=sum_(d<=D) tau(d) << D log(2D).
The fundamental lemma gives, uniformly for every
compatible residue class,

    # idle extensions
      = N_b V (1+O(exp(-s)))
        + O(sqrt(N_b) log(2N_b)).                  (7)

Constants are uniform with the sieve dimension
bound and product-condition constant fixed.
The absolute error divided by N_b V is
O(log(2N_b) (log z)^2/sqrt(N_b)).
This is a two-sided sieve estimate, not merely
an upper bound. Its error is small at small
sifting exponents; it does not justify a
lower bound when s is too small.

Fix 0<delta<1 and assume m<=R^delta. Then
N_b=N/m+O(1) >> R^(1-delta). If z=R^o(1),
s tends to infinity uniformly, so (7) becomes

    # idle extensions = (1+o(1)) (N/m) V.         (8)

In particular the formal-product idle probability
can be transferred with relative error o(1)
even when the PRODUCT of all the primes queried
during the idle segment is much greater than R.
The modulus cap is required only for the PREFIX.
This is stronger than the crude full-query
modulus transfer of 0116e3e for stationary events.

If z<=C R^epsilon for a sufficiently small fixed
epsilon>0 depending on delta, then s is bounded
below by a sufficiently large constant. The
relative sieve error can be made <=1/2 for all
large R (choose epsilon after the absolute
constant in (7)); thus the same count is comparable
to (N/m)V uniformly. No explicit optimized value
of epsilon is claimed.

One may sum (8), or the two-sided constant-factor
version, over disjoint adaptive prefix leaves
with m<=R^delta, then over their allowed residue
classes. Each original leaf has a fixed parity,
fixed G,t0 and Cartesian allowed sets from d577559.
Choose its classes consistent with the old clock
gates and the required future idle window; each
class carries formal probability 1/m when
parity is uniform. With parity fixed use twice
this mass and the corresponding parity-subinterval.
The formal future idle factor is precisely V by
independent unexposed residues. The classes from
disjoint leaves cannot overlap in actual roots
or in the product model. Uniform relative errors
therefore sum relative to the total formal mass,
regardless of the number of leaves. The waiting
length may be chosen separately at each leaf
subject to the uniform horizon and z bounds.
There is no claim of relative transfer for an
arbitrary future word containing many firings.

## 6. Explicit nonempty initial word with a polynomial idle extension

Take j=55 mod 154 (odd, 6 mod 7, 0 mod 11).
At elapsed t=1 the clock is odd, b=4, candidate
3 is ineligible. At t=2 the clock is even,
b=5, candidate 11 would need j=9 mod11, absent.
At t=3 the clock is odd, b=6, candidate 7
fires because j=6 mod7. Thus exactly the
plus-side p=7 event occurs, with wait 3 and
full gain 6. The height after it is 3 again.
The new distance a=6j-6 is 0 mod3, 2 mod7,
5 mod11. No prime dividing 154 nor prime 3
can force a further event.

Apply (7) in the class j=55 mod154 with
t0=3, G=6, h=3 and K=floor(R^epsilon).
The cutoff z=2K+7 satisfies the polynomial
condition for sufficiently small fixed epsilon.
The Euler product V has lower bound
>>1/(log R)^2. Consequently, unconditionally,

    # {A=6j in [R,2R] :
         first event p=7 at elapsed 3,
         no more events through elapsed 3+K}
      >>_epsilon R/(log R)^2.                     (9)

This applies for all sufficiently large R.
Such actual roots have gain 6 through the
whole window and height 3+K at its end.
The same result with empty prefix is classical
two-neighbor roughness expressed in MIN language;
(7)-(9) give a transcript-conditioned extension
including nonempty prescribed histories.

The stationary interval is only polynomial
with a small exponent, or subpolynomial for
the relative asymptotic. It is NOT a linear
fraction of A. In particular the stopped-prefix
W(A) can be large after this window. No lower
sieve in this argument reaches K proportional
to A; (7) then lacks a positive lower-bound
main term. A proof of (9) is not a twin-prime
existence proof. The quantitative new objective
is to extend the stationary transfer across
many subsequent segments while retaining the
small prefix modulus and controlling actual
gains/support, or find a different mechanism
for macroscopic idleness.

## 7. Executed finite audit: adaptive support

Source research/min_local_negative_adaptive_support_gap_audit.mjs,
commit 95d4ffb4cddb2727bcd6dfbf8752feae3e581ab8,
blob b22c1e79f794e24971e21b03a447ec587d195364.
Executed as ECMAScript in research runtime,
fetched at exact commit and re-executed
with identical output. Reproduce using node
on this source. No separate Node or Lean run.

Canonical A=12,18,...,120000: 19999 roots,
355317 events, 19982 strict small-wait finite
witnesses, 6 trajectories without twin source
in the stopped prefix (including final source).
All six lower-bound checks passed. Core-bound
checks on nonempty trimmed blocks as applicable.
Additional noncanonical initial phases 0,17,
floor(R/3) in five slabs R=10000,40000,120000,
250000,500000, 50 initial roots per phase/slab.
Cut at twin sources and half crossing.
750 phase/root controls, 20842 retained events,
714 contiguous non-twin blocks.

    core controls                        4127
    quantitative inequality checks       4127
    short-relay / exception checks       3175
    wall-run checks                     23087
    actual CRT pair keys checked           29
    very-high exception checks           2157
    exact wall-ratio refinements         4127
    strict improvements over
      product-based guaranteed ratio     3408
    synthetic support/threshold checks   2500
    exact large-prime addition checks     282

All final assertions passed. First prototype
attempted to access an unenumerated wall table
when the period exceeded the computational cap.
Final code skips these tables before accessing
them. The quantitative constant used in audit
is deliberately generous (100 on first term,
10 on exception term); finite controls do not
establish sharpness. The actual CRT key count
is small at the selected high-ratio thresholds;
no asymptotic density of sparse cores claimed.

## 8. Executed finite audit: stationary extension

Source research/min_local_negative_stationary_extension_sieve_audit.mjs,
commit 6b89f0f27ee8eed2b3c569020261189646862f60,
blob 80bbd52ee1b4bb0c27fa45f25d2f81ceb9f9e1b7.
Executed in ECMAScript research runtime,
fetched at exact commit and re-executed with
identical output. Reproduce using node.
No separate Node or Lean run.

Direct ordinary event computation compared
against exact forbidden-residue sieve of each
stationary window, for the j=55 mod154 family
and the two parity classes at the initial
state. 21 progression/window controls,
161368 root/window incidences. All prefix
conditions, idle equivalences and roughness
sufficiency checks passed. For up to three
free prime coordinates, 5312 squarefree CRT
remainder checks passed (6), max observed
|r_d|/nu(d)=.698545. Independent actual
variable-prefix controls at t0=1,3,5,8,12,30,60,
2338 prefix incidences, 11690 idle-window checks,
245009 prime forbidden-set checks; all passed.
15135 prefix event evaluations include repeated
progression controls. Unused leaf counters
remain zero; no empirical adaptive-leaf union
simulation claimed.

Example in j=200001..399990, j=55 mod154,
1298 roots:

    K       exact idle count   actual / (N_b V)
    10          583               1.00265
    30          405                .99842
    100         235                .98001
    1000         91                .81845
    5000         79               1.06628

These are finite exact counts, NOT a numerical
proof of (7)-(9) or optimized sieve exponents.
The asymptotic uses the stated standard
fundamental lemma, whose hypotheses were checked
mathematically in sections 4-5. All reusable
artifacts stored on the assigned branch.

## 9. Status and next main bottleneck

The sparse-core obstruction (4) is now uniform
over actual supports without a prescribed
alphabet gap or absence of outliers. The
stationary-extension theorem (7)-(9) gives
unconditional asymptotics/positive counts on
genuine finite physical slabs rather than only
full CRT periods. Neither produces a sparse
core on an unbounded sequence through the
macroscopic stopped horizon. The unresolved
step is the linear-scale gain/wait saving
liminf W(A)/A<1/4 (cc62807), possibly using
successive stationary extensions and actual
adaptive support control. No proof of twin
infinitude, no Lean verification, no changes
to canonical Lean targets or sibling branches.
