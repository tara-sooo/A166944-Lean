# First-significant stopping and disjoint-scale cascade

2026-11-26 JST. Continuation of 10382d81efbbb28b10a5e9847656b8420de72e19.
Focus on the missing medium-dense part of compressed reverse ancestry.
Paper deductions using the inherited primorial wall and two-form
upper sieve, plus an executed finite audit. No Lean kernel check,
novelty claim, or twin-infinitude proof.

## 1. Deficit stops the fast high prefix without a prescribed window

Use ordinary uncut MIN with gain g=p-1, wait w, and deficit
d=2v-u>=0. Each event satisfies w<=2p<=3g. Fix C>=1,
0<=d0<=CT, and divide labels into low p<=y, medium y<p<T,
and high p>=T. Put Q=2 product_(3<=p<=y) p, or use any
valid uniform low-run gain cap in place of Q. The primorial
wall proves the cap Q for every consecutive low run,
independent of phase and starting offset.

Define significant high to mean 8w>=g at a high event.
Examine any finite prefix strictly before the FIRST significant
high event, having at most m medium events. Let L,M,H be its
total gains from low, medium, high respectively, and h its
high-event count. All high events in this prefix are fast
(8w<g). The number of low runs is <=m+h+1, so

    L<=Q(m+h+1), M<=mT, h<=H/(T-1).
    (3/4)H <= d0+5(L+M).                           (1)

The last inequality is exact telescoping d_end=d0+2W-G>=0:
each fast high event spends at least 3g/4 deficit, whereas
each other event produces at most 5g. No assumption of
bounded intermediate deficit, non-twin sources, independent
clocks, or eventual excursion return.

Assume Q<= (T-1)/20. Substituting the low-run bound into
(1) and absorbing 5Q H/(T-1)<=H/4 yields

    H <= 2d0+10mT+10Q(m+1)
      <= (2C+11)(m+1)T.

Consequently h+m<=K=ceil(40(C+1)(m+1)), and the total
prefix gain is < P-1 for P=ceil(100(C+1)(m+1)T).
In particular every preceding non-low label is <=P, and
every preceding offset lies within P of the initial offset.
The constants are deliberately loose. This improves the
prior reverse argument by bounding the prefix length and
labels from the actual deficit balance, not from a separately
chosen D. The first significant high label itself can
exceed P: it is not an event in the preceding prefix.

For any infinite ordinary trajectory this implies that
either the first significant high event occurs, or the
(m+1)-st medium event occurs. Otherwise every prefix would
have uniformly bounded gain, contrary to strict increase.
If the latter happens first, its source is within P of the
initial offset, and its arrival is within P+T. This is
true even when the original path contains twins, since
ordinary uncut MIN always has a next event and preserves
the envelope. One can alternatively stop at a twin source
and treat that as a separate desired terminal outcome.

## 2. A weighted first-bad inverse-degree estimate

As in the preceding note, an inverse non-low edge arriving
at U has label p|U or p|U+2 and source U-p+1. Because of
section 1, it suffices to count p in (y,P]. Let deg_P(U)
be the number of these side/label pairs. Define B>=1 and
call a non-low arrival bad if deg_P(U)>B.

For a target offset, all prefixes with at most K non-low
events, low-run displacements <=Q, and all non-low
arrivals good have at most

    A=(K+1)(Q+1)^(K+1) B^K                            (2)

possible origin offsets. The previous proof of the
compressed inverse graph applies verbatim with restricted
candidate labels. It does not bound actual phase choices,
but we need only count offsets X, even when ANY admissible
initial phase is allowed. The endpoint itself need not be
a non-low arrival: first subtract the last low displacement.

For a prefix with a bad non-low arrival, stop at its FIRST
such arrival U. The last edge can be chosen in deg_P(U)
ways, and the earlier prefix has only good non-low arrivals.
Hence the number of origins that ever hit a bad arrival
before the stopping budget is at most

    A * sum_(R<=U<3R, deg_P(U)>B) deg_P(U).            (3)

This first-hit argument avoids repeatedly multiplying the
large degrees, and works even if many origins coalesce.
It is important to charge the degree at the bad endpoint
once, rather than simply count bad offsets.

Now let z=log log T -> infinity, B=ceil(z^2),
j=floor(B/2)+1. For n>=1 write omega_P(n) for the
number of distinct prime factors <=P. Since
deg_P(U)<=omega_P(U)+omega_P(U+2), and
a+b<=2 max(a,b), on a bad offset at least one of these
counts is >=j. For n>=j, n<=j binom(n,j). Thus the
weighted bad sum in (3) is at most a constant times

    j sum_(n<=3R+2) binom(omega_P(n),j).

When P^j<=R^(1/2), expand the binomial as a sum over
squarefree products of j distinct primes <=P. Counting
multiples and using the prime reciprocal sum yields the
bound

    << j R (log log P+O(1))^j/j! + j P^j.             (4)

For the parameters below log log P=z+O(1), so by
j! >= (j/e)^j the first term is R exp(-Omega(z^2 log z)).
The second term is negligible compared to R exp(-c z^2)
uniformly for T<=sqrt R.

When P^j>R^(1/2), log R<2j log P and therefore
log log R<=z+O(log z). Instead use the unrestricted
omega(n), the elementary divisor bound
2^omega(n)<=tau(n), and sum_(n<=3R+2)tau(n)=O(R log R).
The number of n with omega(n)>=j is O(R log R 2^(-j)).
The uniform omega(n)=O(log R) gives the weighted bound
O(R log^2 R 2^(-j))=R exp(-Omega(z^2)).
Thus in BOTH cases

    sum_bad deg_P(U) << R exp(-c z^2).                (5)

This uniform tail estimate depends on the scale T, not
on a lower bound of T in terms of R. The small-scale
case is what the preceding global divisor-degree bound
could not cover. The first-bad stopping is essential:
multiplying every inverse step by the worst possible
degree would lose the tail in the small-scale range.

## 3. First-significant rarity at arbitrary growing scales

Take any T=T(R) -> infinity with T<=sqrt R. Put
z=log log T, y=floor(z^(1/4)), m=floor(sqrt z).
For sufficiently large T, y>=3 and Q=exp(O(y)) by
Chebyshev, so Q<=(T-1)/20. Fix C>=1 and use K,P of
section 1. Then K=O_C(sqrt z), P=O_C((m+1)T)=o(R).
For any X in [R,2R) all prefixes in section 1 remain
in [R,3R) for sufficiently large R. Equation (2) gives

    log A=O_C(z^(3/4)+sqrt z log z)=o(z).             (6)

Define E_C(R,T) as the set of even X in [R,2R) for
which there exists an envelope-valid starting phase
with d0<=CT whose FIRST significant high event occurs
before the (m+1)-st medium event. This definition has
no prescribed physical crossing length.

The preceding prefix has the deterministic bounds from
section 1. Origins with any bad non-low arrival are
covered by (3),(5),(6), a total O(R exp(-c' z^2)).
All other origins must reach a significant high source
whose two neighbors have no odd prime factor <(T-1)/16:
any such factor q has an eligible clock within 2q ticks,
whereas w>=g/8>=(T-1)/8. The inherited two-form Selberg
upper sieve applied to u-1,u+1 with cutoff floor(T^(1/20))
bounds the number of such offsets in [R,3R) by
O(R/log^2 T). The two forbidden roots modulo each odd
sieve prime are distinct; the O(T^(3/10)) error is absorbed
uniformly because T<=sqrt R. Include twin sources in this
upper bound. Reverse from each rough source using (2).

Together,

    |E_C(R,T)| <<_C R exp(-c' z^2)
      + (R/log^2 T) exp(O_C(z^(3/4)+sqrt z log z))
      = O_C(R exp(-(2-o(1))z)).                     (7)

Equivalently this is R/(log T)^(2-o(1)) up to constants.
All origins and starting phases in the stated deficit
range are covered; there is no averaging of independent
clock probabilities. All asymptotic error terms are
uniform in the displayed T range as T tends to infinity.

This is a first-significant theorem, not a theorem
about arbitrary late significant events after the medium
budget has been consumed. It does imply that for every
X outside E_C, every admissible ordinary trajectory
must encounter m+1 medium events before its first
significant high event, and all these medium events
occur before displacement P+T. This follows from the
deterministic stopping argument of section 1.

A long departure from d in {0,6} with label p>=T is
significant, by the previous departure identity
2w=3p-1+s-d. Thus on typical canonical roots the first
such high-deficit launch cannot bypass this intermediate
scale requirement. This assertion applies to first
significant high supply, not arbitrary descendants of
arithmetic high-launch sources.

## 4. Disjoint scales on the SAME trajectory

The preceding scale barrier (10382d8) allowed multiple
scales, but their medium ranges generally overlapped.
The new uniform range permits disjoint ones.

For any fixed positive J and sufficiently large R, set
T_1=floor(sqrt R), and recursively

    y_i=floor((log log T_i)^(1/4)),
    T_(i+1)=floor(y_i/2), i<J,
    m_i=floor(sqrt(log log T_i)).

Every T_i tends to infinity for fixed J as R tends to
infinity, and the medium bands (y_i,T_i) are pairwise
disjoint. Apply (7) at each scale, with C=1, and take
the union of the finitely many exceptional offset sets.
Its cardinality is o(R). Thus on ALL remaining
canonical resets X=0 mod 6 in [R,2R), the same ordinary
trajectory has at least m_i+1 actual medium events from
EACH disjoint band, within physical displacement
O((m_i+1)T_i) from X, before its first significant high
event at that scale. These counts can be added without
double-counting events. More generally the same
conclusion holds for any deterministic family of
disjoint scales for which the sum of the exceptional
density bounds in (7) is o(1).

This is an unconditional necessary cascade for density
one of canonical roots. It does not require the
finite-twins hypothesis, or assume that a high-deficit
path ever returns. Under finite twins the same cascade
must occur on non-twin trajectories. However the
required event counts are tiny compared to their
available physical distances, and the gain inequalities
are mutually consistent. The theorem gives no
contradiction by itself.

A useful negative conclusion for proof strategy:
one cannot expect to eliminate the residual traffic
merely by asserting that typical roots have sparse
medium bands at some fixed number of these scales.
Such sparsity is itself ruled out on density-one roots.
A proof now needs a quantitative bound on the waits
after the intermediate budgets have been consumed,
or an independently justified construction of atypical
roots with the favorable crossing support. Merely
iterating the FIRST significant theorem after arbitrary
arrivals is invalid: those arrivals may concentrate
in the exceptional sets and have larger deficits.

## 5. Executed diagnostic

Source research/min_local_first_significant_cascade_audit.mjs,
commit 27caf12dbf8e2e22ae8411aac3b33596d06f7eae,
blob 0ba05e6aa7074308d3ef824e4038f06ba0a5e157.
Run: node research/min_local_first_significant_cascade_audit.mjs.
Executed as ECMAScript in the research runtime, fetched by
exact commit and re-executed with identical results.
No Node process or Lean process invoked.

All positive multiples of six in each stated slab
[R,2R), five finite parameter controls, stopping before
first significant high (including twin high) or before
the (m+1)-st medium event. Use exact low-run gain caps
4 for y=3, 14 for y=5 from the earlier audited phase
tables. Diagnostic B=4; asymptotic choices in section 3
are not tested at these small scales.

    R        T    y m   roots   significant stop  medium stop  max prefix gain
    100000   127  3 3   16667       6996             9671           432
    100000   251  3 4   16667       6206            10461           856
    1000000  127  3 4  166667      81805            84862           624
    1000000  503  5 4  166667      65948           100719          1854
    1000000  997  5 5  166667      60720           105947          5520

Total 533335 root/parameter incidences, 3649241
ordinary preceding events and reverse-edge checks,
4182576 deficit budget checks, 2792 literal GCD tick
checks, 417481 first-bad arrival controls, 221675
roughness controls. In each slab independently checked
the weighted-degree tail against the exact binomial
moment sum (section 2), not against an asymptotic
constant. Maximum number of preceding fast high
events on any tested prefix was 1. This is merely
a finite observation, not a universal cap. All
assertions passed. Counts overlap across parameter
choices and shared trajectories. The actual tower-spaced
disjoint scale asymptotics are not inferred from these
finite tests.

No canonical Lean target or sibling branch changed.
The mathematical bottleneck remains the medium-dense
part of actual local transport. No unbounded favorable
reset construction or twin-infinitude proof.
