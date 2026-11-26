# Negative MIN: height-local scan, modulus-budget transfer and complete static walls

2026-11-26 JST. Continuation of d57755967682f5466890019673881d5cbf05171b.
Several connected steps toward the stopped-prefix waiting-time
objective. Replace the scan over all spatial neighbors by a
height-local tick algorithm; transfer adaptive CRT experiments to
finite intervals with an explicit modulus budget; identify every
phase-independent static wall for a finite alphabet, not merely
the primorial multiples. Derive a sharper spatial potential and
low-label gain budget. Paper arguments, exact finite audits and
explicitly identified formal-product simulations. No asymptotic
twin-infinitude theorem or Lean verification.

## 1. Height-local candidate scan

Canonical A=6j, v0=3-3j. At elapsed tick t, let G be the
cumulative gain BEFORE processing this tick, so the actual
clock is n=3-3j+t and the source remaining distance is a=6j-G.
Write the pre-firing height

    b=a/2+n=3+t-G/2.

At an even clock n, only a minus-side event may fire:
p|a+1 and n=0 mod 2p. Therefore p divides 2b+1.
At an odd clock n, only a plus-side event may fire:
p|a-1 and n=p+2 mod 2p. Therefore p divides 2b-5.

Conversely if an odd prime p divides the relevant height
expression and the indicated clock fires, the corresponding
spatial divisibility holds. Thus it is enough to factor
ONE odd integer per tick (use its absolute value if
negative), test the clock condition for its prime factors
in increasing order, and select the first success.
If there is no success the tick is idle. No factorization
of a potentially enormous a-1 or a+1 is needed.

For fixed j parity epsilon, the tick parity is determined.
Write e=-1 for even/minus, +1 for odd/plus, and c(p,e)=0
or p+2 respectively. For p>=5 a candidate query is simply

    j = inverse(3,p)*(3+t-c(p,e)) mod p.            (1)

For p=3 use the deterministic test
3+t-c(3,e)=0 mod3. The appropriate clock parity has
already been enforced. Note that p=3 cannot be treated
by inversion of 3.

After the tick the new height is b if idle, or
b-(p-1)/2 if an event occurs. With initial height 3,
the update preserves nonnegativity: b>=1, and the
candidate p is at most 2b+1 (for b=1 the possible
negative plus expression is -3). Inductively

    0<=h_t<=3+t,  G_t=2(3+t-h_t)<=2t+6.
    Every queried prime at tick t is <=2t+7.        (2)

This gives a formal process on any specification
of one residue j mod p for every p>=5, plus parity.
It agrees exactly with the actual physical process
before the prescribed half-distance/time stop.
For any fixed horizon K, it is fully determined
by finitely many primes <=2K+7; any formal
residue environment for that horizon has arbitrarily
large actual canonical representatives by CRT.
This last observation is not a relation between
K and the size of the representatives.

For a physical initial-root interval with A much
larger than K, no half-distance crossing or clock
stop can happen before K by (2) and the initial
clock. The height scan therefore agrees over the
whole horizon without any conditioning on a
physical stopping event.

## 2. Transfer with an adaptive modulus budget

Fix parity, write j=2l+epsilon, and compare the
formal probability measure (independent uniform
residues for p>=5) with l uniform on an interval
of N consecutive integers. Use any finite adaptive
prime-query tree as in d577559, for example the
height scan in section 1. Include negative as well
as positive queries. Stop BEFORE exposing a new
prime if the product of exposed distinct primes
would exceed a specified budget B.

Each terminal leaf L has a definite exposed prime
set, modulus Q_L, and allowed residue sets C_q.
Its event is exactly a union of M_L=prod|C_q|
classes mod Q_L in l; unexposed coordinates are
unconstrained. The modulus and allowed sets may
depend on the entire earlier query transcript.
The deterministic gates have already been applied.
In the product measure

    P(L)=M_L/Q_L.

Let P_I(L) denote its actual interval probability.
Every residue count differs from N/Q_L by at
most one. Consequently

    |P_I(L)-P(L)| <= (Q_L/N) P(L).                 (3)

This is a relative, not an additive-per-leaf,
error. All leaves are disjoint in BOTH models.
Summing (3) gives the total variation bound

    TV(P_I,P) <= E_P[Q_L]/(2N) <= B/(2N).          (4)

It is independent of the number of leaves. No
common product of all primes used on all branches
is needed. A reward in [0,1] determined by the
capped transcript has expectation error at most (4).

If an original finite-horizon transcript is
truncated at the modulus cap, let rho be its
formal probability of hitting the cap. By coupling
the capped leaves maximally and then extending
the two models conditionally, full-horizon output
TV is bounded by rho+B/(2N): on a matched,
non-capped leaf the original output is identical,
and the matched capped leaves have total mass
at most rho. This bound requires both models'
uncapped outputs to be well-defined; in particular
the physical stop must not intervene if one
wants the same fixed-horizon height algorithm.

For example, by Chebyshev's bound for the sum
of log primes, the product of primes <=2K+7
is exp(O(K)). If K<=c log N for sufficiently
small c, the whole height transcript transfers
with error o(1). This is a genuine finite-interval
adaptive law but at logarithmic, not linear,
elapsed time. More generally (4) handles a
path-dependent product cap even if the possible
global alphabet is much larger.

## 3. Exact formal first-wait heavy tail

Consider the first firing from canonical A=6j
and fix parity. On an idle segment G=0, the
height scan's negative queries for a given p>=5
can only concern the two residues 6j=+/-1 mod p.
Let nu_p(K) be the number of distinct such
residues queried through tick K assuming no
firing so far. Then nu_p is 0,1,2 and is zero
for p>2K+7 by (2). Prime 3 is ineligible.
The exact formal probability of first wait >K is

    S(K)=prod_(p>=5)(1-nu_p(K)/p).                 (5)

For p<=K/2 both possible sides have had a
first clock opportunity, since every candidate
wait is <=2p. Thus nu_p(K)=2 on this range.
It follows that

    prod_(5<=p<=2K+7)(1-2/p)
      <= S(K) <= prod_(5<=p<=K/2)(1-2/p).

By Mertens' theorem and the convergent product
of (1-1/(p-1)^2), both bounds have the SAME
asymptotic

    S(K) ~ C_*/(log K)^2,
    C_*=9 exp(-2 gamma) prod_(p>=5)(1-1/(p-1)^2)>0.   (6)

In particular the first wait in the formal
product model is almost surely finite but has
infinite expectation. The statement holds
for both parities; it is not a statement about
the mean of actual waits in a short physical slab.

The argument also gives a conditional dichotomy
after any finite nonempty exact transcript.
Let F be the finite set of exposed primes >=5,
with allowed sets C_q. Keep the current state
and clock fixed by the transcript's G,W in
the affine representation. At each q in F
let k_q be the number of the current two
eligibility residues in C_q. If q=3 is
eligible, or some k_q=|C_q|, an old clock
must fire within a fixed finite time (or be
preempted by an earlier clock), so the next
wait is bounded. Otherwise the probability
of avoiding all old eligible clocks is

    c_old=prod_(q in F)(1-k_q/|C_q|)>0.

For K large enough all old clock opportunities
have occurred; the unexposed primes remain
independent uniform. The same sandwich as
above, now with the finite set F removed and
candidate cutoff 2K+O(current height), gives

    P(next wait>K | transcript)
      ~ c_old C_* prod_(q in F)(1-2/q)^(-1)
                        /(log K)^2.               (7)

Thus that conditional wait again has infinite
formal mean. This does not establish how often
such a transcript occurs, nor independence
between successive waits.

For every fixed even cumulative gain G, almost
surely infinitely many fresh primes p satisfy
one of 6j-G=+/-1 mod p in the product environment,
by independence and divergence of sum 1/p.
Intersect over countably many G. The process
therefore cannot become permanently idle:
if it did, G would remain fixed and any eligible
prime would eventually fire. In fact infinitely
many distinct labels must fire almost surely,
by the finite-alphabet wall bound below.
This is compatible with heavy-tailed long idle
segments and does not imply physical twin
infinitude.

## 4. Complete phase-independent static walls

Use half-distance x=a/2. An odd-prime event p
has half-gain g=(p-1)/2, source 2x=+/-1 mod p,
and arrival x-g. For a wall coordinate J,
a jump crosses strictly from x>=J to x-g<J
exactly when its source x=J+d has 0<=d<g.
Eligibility in x is x=(p-1)/2 or (p+1)/2 mod p.
As d ranges from 0 through g-1, the forbidden
wall residues are precisely 1,2,...,(p+1)/2.
Consequently the EXACT wall condition for all
spatially eligible p jumps, regardless of phase
or priority, is

    (-J mod p) <= (p-3)/2.                        (8)

This is the stronger half-line barrier property:
a jump can land exactly at J, but cannot pass
from x>=J to x<J, including a jump starting at J.
In particular J itself is ineligible for p.
The term "complete" here refers to spatially
eligible jumps, not to additional walls that
could exist for particular clock phases.

For a finite odd-prime alphabet A0, define

    Q=prod_(p in A0)p,
    Wall(A0)={J in Z: (8) holds for every p in A0}.

The set is periodic mod Q, contains 0, and has
exactly

    prod_(p in A0)(p-1)/2

wall residues per period by CRT. Thus its density
among half-distances is 2^(-|A0|) prod(1-1/p).
The old primorial-multiple wall is only one
of these residues. Let M be the maximum gap
between successive walls (in half-distance).
Then 1<=M<=Q, and every contiguous A0-only
run has full gain at most 2(M-1), or <=2M
with a simpler weak bound. The run lies above
the wall immediately below its initial source;
it cannot enter the next lower wall cell.
This holds even with omitted clocks competing
in the full MIN, provided all actual selected
events of the run belong to A0.

The finite wall also bounds the total gain
of any formal trajectory using a fixed finite
alphabet: define distance to preceding wall
from the formal residue x=3j-G/2 mod Q.
Each selected jump decreases this nonnegative
periodic distance by exactly its half-gain.
For p=3 the half-distance residue is fixed
by G, so no j mod3 coordinate is needed.
Thus such a trajectory has finitely many
events. Combined with section 3, the formal
product trajectory has infinitely many
distinct selected primes almost surely.

## 5. Sharper total low-gain budget: wall cells and potential

Consider any actual decreasing event block.
Call events using A0 low and all other events
high, with high-event count h. Let G_low be
the FULL gain from low events. Partition the
half-distance interval between block endpoints
into the wall cells, clipping the two boundary
cells to the interval. Each low-only run stays
in one cell, and the traversed subintervals
in each cell are disjoint by monotonicity.
At most h+1 distinct cells can carry low gain.

If the clipped cell lengths sorted decreasingly
are d_(1)>=d_(2)>=..., then

    G_low/2 <= sum_(i<=h+1) d_(i)
             <= M(h+1).                          (9)

Equivalently, for every real B>=0,

    G_low/2 <= B(h+1)+sum_cells (d_i-B)_+.         (10)

This uses the entire physical interval, not
a worst-case gap for every run. In a periodic
alphabet, with full cell lengths d_i in one
period, define Psi(B)=Q^(-1)sum_(period)(d_i-B)_+.
For a physical half-distance interval of
length D, the tail term in (10) is at most
(floor(D/Q)+2)Q Psi(B), by splitting at the
period boundaries. For short intervals the
exact clipped cells may be much better.

An alternative exact accounting is the wall
distance potential

    J(x)=largest wall <=x,
    d(x)=x-J(x),  0<=d(x)<=M-1.

For every event x->y=x-g let C=J(x)-J(y)>=0.
Then d(y)-d(x)=-g+C. For low events C=0.
Consequently over the whole block,

    G_low/2=d(x_start)-d(x_end)
                    +sum_high [d(y)-d(x)]
      <= d(x_start)+sum_high [d(y)-d(x)]_+.       (11)

A high event in the same wall cell cannot
recharge this potential. If its half-gain is
0 mod Q, the recharge is zero even if it
crosses many walls.

There is a simple one-sided residue refinement.
For integer s>=0, d(x+s)<=d(x)+s because J is
nondecreasing. By periodicity, for a high p
put

    s_p=(-(p-1)/2 mod Q),  0<=s_p<Q.

Then

    d(y)-d(x)<=min(s_p,M-1).

For s_p<M this is the exact maximum over the
full residue space: start at a wall followed
by a gap of length M. For s_p>=M it is only
an upper bound. Zero maximum occurs only
when s_p=0: a shift of zero maximum has zero
mean change over the period, hence leaves d
and its zero set invariant; the individual
nonempty proper wall sets mod each prime
have no nontrivial period, so CRT forces
the shift to be zero mod Q.

Thus (11) implies the residue-sensitive bound

    G_low <= 2d(x_start)
                 +2 sum_high min(s_p,M-1).        (12)

In particular p=1 mod 2Q is neutral, while
p=-1 mod 2Q can recharge at most one unit
of half-gain, regardless of the size of p.
More generally this is a one-sided neighborhood
of the neutral class, not just a single residue.

## 6. Connection to existing prefix bounds

Suppose all selected labels <T of an actual
block belong to A0. All relays between
consecutive high labels have full gain <=2M,
and if 2M<T-1 they cannot connect identical
high labels (755b0ce). For a non-twin block
of full distance width D=R in [R,2R], h<=
R/(T-1)+1. The wait bound from 755b0ce now
works with 2M in place of the old 2Q
primorial wall bound. In particular for
T=R^theta, 0<theta<=1/2, M=o(T), and
macroscopic completed wait W>=eta R,

    L >>_eta sqrt(T/(M+1))

is necessary, with L the number of distinct
high labels. All constants are as in the
short-relay CRT argument. This replaces
a condition on the full period by one on
the actual wall gap. It is not yet an
unconditional bound on M for a growing
alphabet.

Alternatively the quadratic relay bound
of 567028a does not require 2M<T-1.
At T comparable to sqrt A, put J equal
to the actual distinct ordered unequal
high-pair/sign key count. A sufficient
condition on a non-twin stopped prefix
to have W=o(A) is

    J=o(sqrt A),
    (J+1)(d(x_start)+sum_high min(s_p,M-1))=o(A).

This follows from (12) and the joint
single-threshold criterion. It makes the
dependence of lower-label gain on the
actual high-label residue sequence
explicit, not just on their count.
No unbounded sequence satisfying this
condition has been constructed.

The stopped-prefix gain itself has an
equivalent target at sublinear scale:
for standard roots, G<=2W+6 by height,
and W<=3G by the per-event wait bound.
Together with cc62807, infinitely many
twin primes iff liminf G(A)/A=0, and
liminf G(A)/A<1/12 is sufficient
(using W>=A/4-O(sqrt A) under finite twins).
This is for the original completed-event
prefix, not a macro-time count that
includes the unfinished final idle wait.

## 7. Uniform escape from a bounded height strip

Fix integer H>3 and let tau_H be the first
elapsed tick with h_t>=H in the formal
height scan. Up to and including this
first crossing, b<=H (height increases
by at most one per tick). Thus every
queried and selected prime is <=2H+1.
Use the alphabet A0 of all odd primes
<=2H+1, and the wall distance d of
section 5. Before reaching H, the
half-gain is at most d(x_start). By
h_t=3+t-G_t/2, necessarily

    tau_H <= H-3+d(x_start) <= H-3+M-1.           (13)

Indeed if still below H at that time,
the gain bound would force h_t>=H.
This applies to every formal residue
environment by the finite periodic
description. Therefore formal heights
are unbounded even without randomness.

The hitting-time distribution is determined
by the fixed parity and primes <=2H+1,
without any product over later primes.
In particular for physical initial roots
in an interval of scale N, choose H a
sufficiently small constant times log N.
The period product is <=N^delta for some
fixed delta<1 (using Chebyshev), and (13)
is O(N^delta+log N), so physical stopping
cannot intervene on large roots of
comparable size. Equation (4) transfers
the exact formal hitting-time distribution
with o(1) error. This is a uniform
logarithmic-height escape result, not a
macroscopic W/A saving.

## 8. Executed audits and persistence

Height scan / modulus transfer / formal waiting:
research/min_local_negative_height_local_scan_audit.mjs
commit 8cd64a9ea15849764b5a87915421ce0c08b8c1ac,
blob 2c329f2b764ae6adbdd215250c19bcf6c6bdecab.
Executed in ECMAScript research runtime; exact
remote readback re-executed with identical output.
Reproduce with node on the above source.
The first prototype failed because its factor
table could overwrite smaller factors, causing
a tick scan to try a larger prime before 3.
The final table retains the least factor;
all final comparisons pass. The event-jump
reference uses explicit lexicographic minima.

    actual roots                      1212
    actual ticks / height checks     1806735
    actual completed events           24830
    prime queries                     2679835
    first-wait residue checks          428844
    first-wait full-period checks      409165
    capped tree controls                    8
    disjoint capped leaves                121
    interval root partition checks     328000
    per-leaf relative error checks       363

Actual A=120,318,...<=240000, first min(1500,A/2-4)
ticks, stopping on half crossing. Tick-level
outputs agree with the ordinary event rule.
The capped trees use horizons 8,12,18,22
and modulus caps 35,385,1155,5005 for
both parities; interval lengths 1000,10000,
30000. All exact partition and relative
error checks pass. Max observed TV/theorem
upper bound is 0.02915. At horizon 22 with
cap 5005 the probability of reaching
the horizon without cap is only about
0.00261 or 0.00360 depending on parity.
Hence a small transfer error for the
capped process does NOT imply a small
error for the original full process.

First-wait products tested at K=4,6,8,
12,20,100,1000,10000,100000, both parities.
Complete period enumeration where the
product is <=500000; all exact comparisons
and sandwich checks pass. For parity 0,
formal first-wait survival:

    K       probability       probability*log(K)^2
    100       0.107966             2.28969
    1000      0.050061             2.38874
    10000     0.028592             2.42547
    100000    0.018414             2.44075

Conditional asymptotic (7) follows from
the same arithmetic, not from a separate
large conditional Monte Carlo experiment.

Additional explicitly FORMAL product-residue
simulations with fixed deterministic PRNG seed:
240 runs at each of K=100,1000,10000,
80 runs at K=100000; 800 runs total.
Each queried prime receives a pseudorandom
uniform residue once, retained forever;
not physical roots at scale K.

    K       mean h_K/K  mean G_K/K  mean last-event/K  mean log Q
    100       .699167     .661667       .474250          91.48
    1000      .731338     .543325       .366458        1024.28
    10000     .811043     .378515       .263976       11409.23
    100000    .860552     .278956       .202869      119297.04

These are descriptive finite formal
samples only. In particular log Q is
already linear-scale in the horizon in
these samples. Transferring such a model
at K comparable to a physical A via
(4) is not justified. No claim that
last-event/K or gain/K tends to zero.

Enhanced static walls / cell budgets:
research/min_local_negative_enhanced_wall_budget_audit.mjs
commit 6d00cf27da7fe31fb951664786f4228612bf8398,
blob fcdbe458946358d81477f28610b31c80afe81f54.
Executed in ECMAScript research runtime;
exact remote readback re-executed with
identical output. Reproduce with node on
the above source.

For all odd primes through z, exact wall
sets enumerated by CRT, sorted and all
cyclic gaps checked (half-distance units):

    z       Q             wall residues    max gap M
    3       3                   1              3
    5       15                  2              9
    7       105                 6             54
    11      1155               30             99
    13      15015             180            219
    17      255255           1440            714
    19      4849845         12960           1785
    23      111546435      142560           5355
    29      3234846615     1995840          18885

These are exact finite maxima for the
specified static wall sets. They are not
asymptotic bounds on growing z. The
script records full gap histograms via
counts and evaluates tail masses at
several multiples of the mean gap.

    local wall iff comparisons            127
    CRT wall residue lifts              2153019
    gap checks                          2153019
    actual event evaluations               3918
    contiguous blocks                       239
    low event wall checks                 24764
    low-run counts across cutoffs          8291
    cell-budget checks                     2151
    strict cell vs max-gap improvement     2103
    wall potential telescopes              2151
    individual wall-drop checks           35262
    neutral high-event checks              1170
    tail-budget checks                     6453
    one-sided recharge checks           1355782
    exact short-shift maxima checks         165

Actual blocks use even initial distances
in the four slabs R=10000,40000,120000,180000
with initial phase 3-A/2 or 17. Some of
these initial distances are not multiples
of six; these are local controls, not
all canonical seeds. The spatial bounds
need neither canonical phase nor absence
of twins. Full residue recharge maxima
checked for z=3,5,7,11. All assertions pass.

For fixed bounded-height targets H=4..8,
enumerate the complete canonical periods
(including parity) of all relevant primes.
191030 initial residues, 1335732 ticks,
all (13) checks passed. Exact escape
statistics over these full periods:

    H       mean escape ticks    max escape ticks
    4          1                    1
    5          2.68182             14
    6          4.23836             24
    7          5.54615             25
    8          7.26129             38

The wall bound is much looser than the
actual maximum here, e.g. max wall bound
716 at H=8. No uniform polynomial escape
bound is claimed.

No separate Node or Lean process invoked.
Both scripts are actual reusable source
files committed on the assigned branch.

## 9. Remaining research target

The phase-local scan is exact and the
adaptive finite-interval error no longer
pays for the number of leaves. The new
static walls are much denser than the
primorial multiples and give a spatial
resource budget including high-label
residues. The formal waiting distribution
has a rigorously heavy tail. However
neither formal long idle segments nor
the finite wall data imply actual
macroscopic idle segments on unbounded
canonical roots. The remaining needs
are a growing-cutoff wall-gap or
recharge estimate coupled to actual
high-word diversity, or a finite-
interval transfer mechanism that does
not require an exponentially large
query product. The required stopped-
prefix liminf W(A)/A<1/4, twin infinitude
and Lean verification remain open.
No canonical Lean targets or sibling
branches changed.
