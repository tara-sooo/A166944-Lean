# Weighted inverse kernel and cumulative medium-gain traffic

2026-11-26 JST. Continuation of d876b86829a94da7a0f464c8ff9aeb36676c7919.
Replace unweighted phase-fiber branching and a fixed short-tail cutoff by
a dyadic weighted inverse kernel. Bound whole local origin traffic under
a cumulative lower-scale gain budget, allowing arbitrary high waits,
zero strata, repeated labels, all phases and actual mergers. Also derive
a conditional energy bound for already-formed entry cohorts.
Paper deductions and executed finite diagnostics; no Lean kernel
verification, novelty claim, or twin-infinitude proof.

## 1. Marked high arrivals

Work with ordinary uncut MIN. An event at even offset x and
pre-time v selects an odd prime p with wait w, gain g=p-1,
and arrival (U,n)=(x+g,v+w). Every event has w<=2p<=3g.
The envelope is u/2<=v<=u+1 along the ordinary trajectory.
Set a high cutoff T>=3, and call ALL labels p<T lower
(including the small labels; no fixed low alphabet).

Mark each high arrival by (U,n,p,e), with e=+1 for the
minus-neighbor/even clock and e=-1 for the plus-neighbor/odd
clock. The mark determines its source x=U-p+1. Even arrival
offsets and actual firing phases satisfy

    e=+1: U=0 mod 2p, n=0 mod 2p;
    e=-1: U=-2 mod 2p, n=p+2 mod 2p.

The mark is useful even at deficit 0 or 6, where the state
alone need not uniquely identify a high label. Two marks
with the same state have the same ordinary future. We do
not discard such alternatives or presume phase injectivity.

For any even u in [R,3R), the total number of possible
high side/prime pairs at arrival u is bounded by

    J = 2 ceil(log(3R+2)/log T),

because p>=T divides u or u+2. For each pair its arrival
times lie in ONE residue class modulo 2p. This is an
unconditional divisor bound, not a typical-degree estimate.

## 2. A dyadic weighted inverse transition kernel

Fix any integer B>=1, a gain scale, and define

    c(E,t)=floor(E/B)+floor(t/T),
    weight(E,t)=2^(-c(E,t)).

At a given target high mark (U,n,p,e), the source offset
x=U-p+1 is known. A previous high mark (u,v,r,f) can lead
to the target by a tail of lower events followed by the
current high event. Then

    E=x-u>=0, t=n-v>=1.

E is exactly the total gain of the intervening lower
events, regardless of their number, label diversity,
or physical length. t is the total elapsed time,
including the target event's wait. The path is unique
given its previous state, by ordinary determinism.
For an UPPER bound allow all even u<=x in the slab,
all high side/prime factors of u or u+2, and all
integers v<n in their required arrival phase class,
even if no legal intervening tail or envelope exists.

For fixed u,r,f, consecutive admissible v differ by 2r
and hence the corresponding values floor((n-v)/T)
differ by at least 2. The smallest cost is nonnegative.
Thus their time-weight sum is at most

    1+1/4+1/16+... = 4/3.

Similarly

    sum_(E even >=0) 2^(-floor(E/B)) <= B+2,

because each interval [kB,(k+1)B) has at most ceil(B/2)
even integers and the geometric sum over k is 2.
Consequently every target has total incoming relaxed
weight at most

    C = (4/3) J (B+2).                              (1)

The same bound applies at a fictitious endpoint (x,n)
with no current high mark, using the last high arrival
u<=x as the predecessor and requiring v<n. This bound
does not depend on the number of phases of an actual
clock fiber, and does not require the close-offset
exception set of the previous note. Long waits are
permitted; they pay a proportionally smaller weight.

A direct initial entry from a canonical root X=0 mod6,
v0=X/2+3, to the source of the first high event has
E0=x-X, t0=n-v0. There is only one reset time per X.
Its summed weight over all possible X is <=B+2, since
the time-weight factor is <=1. The same bound holds
for a path with no high event at a fictitious endpoint.

An additional exact observation: if previous and current
high labels are the same p, then the previous arrival
u is 0 or -2 mod 2p, while the current source x is
p+1 or p-1 mod 2p. Therefore E=x-u is in one of the
classes p-1,p+1,p+3 mod 2p. For p>=5, E>=p-1.
Thus same-label consecutive high events need at least
p-1 lower gain between them. This is independent of
phase, orientation, and whether the intervening labels
are small. It is not needed in (1).

## 3. Full reverse word count with two additive budgets

Fix a target high mark and exactly h>=1 high events
in a canonical-origin history ending there. The
preceding h-1 inverse steps have kernel (1); the
initial root entry has summed weight <=B+2.
Induct on reverse word length (all sums nonnegative):

    sum_(actual roots with h high events)
       2^(-sum_edge c(E,t)) <= (B+2) C^(h-1).        (2)

This is a sum over actual distinct root histories;
enlarging to all candidate inverse words can only
increase it. It is not a product of independent
clock probabilities. The physical event graph is
acyclic in offset and the forward word of each
canonical origin is unique.

For a fixed offset x and a common fictitious time n
greater than all phases of interest at x, the same
argument using one final fictitious inverse step gives

    sum_(actual roots with h preceding high events)
       2^(-sum_edge c(E,t)) <= (B+2) C^h, h>=0.      (3)

The cost telescopes in elapsed time and lower gain:
for a history from (X,v0) to x, with total lower gain M_x,

    sum_edge c(E,t) <= (n-v0)/T + M_x/B.             (4)

The final fictitious edge includes the remaining
lower-event tail, possibly empty, and the artificial
time from the last mark to n. It need not be a real
event. Formula (4) is a deterministic inequality
from floor(a)+floor(b)<=a+b, with no phase assumption.

## 4. Uniform origin mass in a local crossing

Take all canonical roots X in [R,2R), 6|X, and a
local crossing width D<=R (positive integer). Consider
visits to any pre-offset x<X+D for which the
cumulative gain from p<T events is <=M.
The total preceding physical gain x-X<D, so all
preceding offsets lie in [R,3R), and

    h <= H=floor((D-1)/(T-1)).

Choose n*=x/2+3D+4. Every actual phase v at x satisfies
v<=v0+3(x-X)<=x/2+3+5D/2<n*, and
n*-v0<=(7/2)D+1. For each root, use (3)-(4) at n*,
then sum h<=H. Since C>=2, the number b_M(x) of
distinct such canonical origins satisfies

    b_M(x) <= 2(B+2) C^H
              * 2^(((7/2)D+1)/T + M/B).            (5)

This is an OFFSET traffic bound, covering all
possible phases at that offset. It does not limit
the number of lower events individually, does not
require that only the first significant high event
be considered, and handles all actual mergers
within these prefixes. In particular no first-bad
inverse-degree stopping or phase-exception removal
is necessary. It allows zero-stratum arrivals by
retaining their incoming label marks.

Choose B=max(1,ceil(M/(H+1))). For T>=R^epsilon,
fixed epsilon>0, J=O_epsilon(1), D/T=O(H+1).
With natural logarithms (5) yields

    log max_x b_M(x)
      <= (H+1) log(2+M/(H+1)) + O_epsilon(H+1).     (6)

No hidden constant multiplies the leading logarithm.
The O term contains the constant in C, the time
cost and the integer rounding of B.
For h=0 one can directly use floor(M/6)+1; the
unified formula is intentionally a slightly looser
bound. The finite constants in (5) are also loose.

## 5. Aggregate wait up to a growing cumulative lower-gain budget

Use the inherited arithmetic bound (paper deduction)
from 2026-11-26-min-simple-crossing-rough-flux.md,
section 2, for non-twin even offsets x in [R,3R):

    q(x)=min(lpf(x-1),lpf(x+1)),
    sum_x q(x) << R^(3/2)/log^3 R.                 (7)

For clarity, the extra third logarithm uses both
neighbors' roughness and the existence of a
composite neighbor. Small q<=O(R^(1/3)) contributes
O(R^(4/3)). At q in a dyadic band [L,2L) above that
scale, choose a composite neighbor n=p k with
p=lpf(n)>=q and p<=sqrt(3R+1); k and pk+/-2 are
both L-rough. The inherited two-form Selberg upper
sieve gives O(R/(p log^2 R)) candidates per p and
sign. Sum over p>=L using the prime reciprocal
upper bound per dyadic band, then weight by 2L;
the resulting convergent geometric series gives (7).
No lower sieve or twin-prime asymptotic is used.

From each reset stop before a twin source, before
the next lower event would make cumulative lower
gain exceed M, or at the first arrival >=X+D.
The stop before a lower event is important: do not
charge that event's wait to this truncated prefix.
At every executed source the preceding lower gain
is <=M. By w<=2q(x), (5) and (7) give

    sum_(all roots) W_truncated
        <= 2 max_x b_M(x) sum_(non-twin x) q(x)
        << max_x b_M(x) R^(3/2)/log^3 R.            (8)

This treats ALL waits simultaneously, including
many significant high events, and every lower
event before the gain budget is exhausted. It
does not require a small final event gain: the
last event is counted at its PRE-offset. Thus
overshooting exits cause no error in (8).
A completed non-twin local crossing has
W>=D/2-3 by the envelope and canonical reset.
Hence the number of these crossings completed
with cumulative lower gain <=M is

    << max_x b_M(x) R^(3/2)/(D log^3 R)             (9)

for D tending to infinity.

Example 1. Let D=T=ceil(sqrt R), so H=1, and
M=floor((log R)^a), fixed 0<a<3/2. Equations
(6)-(8) give max b_M=O((log R)^(2a)),
and total truncated wait o(RD). Thus only o(R)
canonical roots complete a non-twin crossing
with this lower-gain budget.

Example 2. Write z=loglog R, choose fixed
0<beta<1, 0<c<3, T=ceil(sqrt R),
D=ceil(sqrt R*z^beta),
M=floor(exp(c*z^(1-beta))). Then H=(1+o(1))z^beta
and (6) gives log max b_M <= (c+o(1))z.
Consequently (8) is o(RD), and (9) is o(R).
For beta=1/2 this permits cumulative lower gain
growing like exp(c sqrt(loglog R)), with no
separate bound on the number of intervening events.

More generally (8) applies whenever the explicit
bound (5) is o(D log^3 R/sqrt R), in particular
when H=o(loglog R) and the main term in (6) is
at most (3-delta)loglog R for fixed delta>0
and D>=sqrt R. This extends earlier early-prefix
scarcity to a lower-scale PHYSICAL GAIN budget;
the earlier count-budget results are not implied
in parameter regimes where they permit much
larger lower gain.

Under the finite-twins hypothesis, for sufficiently
large R all these trajectories are non-twin in
their local windows. Then density-one canonical
roots MUST exceed M in lower gain before completing
the crossing. This is a necessity, not a contradiction.
It locates the surviving traffic after the cumulative
gain budget, rather than after a fixed number of
medium events. No estimate forcing that surviving
gain or wait to be o(D) has been obtained.

## 6. Energy amplification for previously formed cohorts

The inverse kernel also applies when roots enter
the high-arrival graph from arbitrary earlier
histories. For a specified terminal high mark,
count possible distinct high-marked entry states
connected by at most H high-to-high steps, with
total intervening lower gain <=M and elapsed
time <=W0. Ignore entry ancestry completely.
All preceding marked offsets are in [R,3R).
Equations (1),(4) and the same reverse induction
give the number of such entry marks at most

    A=2 C^H 2^(W0/T+M/B).                          (10)

Here the zero-length path from the terminal to
itself is included. There is no root-entry factor
B+2. The estimate is for the number of entry
marks, not the number of origins already in them.
If a set of distinct entry marks carries disjoint
cohorts with masses m_i, and a deterministic
stopping rule sends each mark to at most one
terminal mark with these budgets, let b_j be the
sum of its incoming cohort masses. Then

    max_j b_j <= A max_i m_i,
    sum_j b_j^2 <= A sum_i m_i^2.                  (11)

Indeed each terminal fiber contains at most A
distinct marks and Cauchy-Schwarz applies to that
fiber; the fibers of the stopping rule are disjoint.
This is a conditional amplification estimate for
an already-concentrated population, including
mergers, not an assumption of equal incoming masses
or a bound on cumulative energy of every visit
along an untruncated path. When T is comparable
to sqrt R, H=o(loglog R), W0=O(HT+T),
and (H+1)log(2+M/(H+1))=o(loglog R), choose B as
before: A=(log R)^o(1). The high graph cannot
amplify the entrance energy by more than this
factor within the specified budgets. To use this
for a proof, an independent bound on the entry
energy (or on the long lower-gain transport
between such blocks) is still needed.

## 7. Executed audit

Source: research/min_local_weighted_inverse_ancestry_audit.mjs
commit 7e80530fd988e01ce2c5a233fac95849c45990fc,
blob 1ae72454c3bd3d26af2d11aec509773cce902ad3.
Reproduction: node research/min_local_weighted_inverse_ancestry_audit.mjs.
Actual ECMAScript execution in the research tool runtime,
exact remote readback and re-execution with identical counts.
No Node process or Lean process invoked here.

Five finite controls, all canonical multiples of six
in [R,2R), stopped before twin, local exit, or lower-gain
budget exhaustion as in section 5:

    R        T     D    M    roots    events  budget stops twin stops  exits
    10000     53   200   16     1667      3159      1312       331       24
    100000   157   633   48    16667     70418     12452      4022      193
    100000   251   633   64    16667     77868     12273      4233      161
    1000000  503  2000   64   166667    789503    135745     30144      778
    1000000  997  2000  128   166667   1139879    124595     41341      731

Totals: 368335 root/parameter incidences, 2080827
ordinary events, 27796 high and 2053031 lower
events. 286377 budget stops, 80071 twin stops and
1887 completed non-twin exits. 2108623 exact
floor-cost/elapsed-time/gain checks; 571621 offset
partition cells and 6269 marked arrival partition
cells checked against the weighted bounds.
100 independently enumerated relaxed inverse
kernels at largest traffic offsets (all candidate
high factor/side pairs and every admissible
envelope phase in the tested physical window),
100 direct root-entry sums, and 889 literal GCD
ticks. All assertions passed. The independent
kernel test uses envelope and finite physical
window restrictions; the analytic bound (1)
permits the larger unrestricted time class.
Total truncated wait 33140799. At R=1000000,
T=997,D=2000,M=128 the maximum offset mass was 40,
maximum first-high arrival mass 22, and maximum
distinct first-high marks at one visited offset 2.
For T=503 at the same R,D, M=64 these maxima were
24,11,4. The five maximum offset masses were
9,25,21,24,40. The explicit upper bounds (5)
are extremely loose at these finite scales;
the five log2 bounds are approximately
37.57,49.84,32.49,44.60,33.47. No numerical
asymptotic constant or absence of late traffic
is inferred. Counts overlap across parameter
choices and shared trajectories.

## 8. Remaining mathematical bottleneck

The previous phase-spacing approach separated
short-wait unique edges from long-wait branches.
Here (1)-(6) account for all branches without
such a separation, and (8) bounds their actual
origin-weighted waiting traffic up to a cumulative
lower-gain cutoff. The missing step is now the
flow AFTER the lower-gain cutoff, or an independent
entry-mass/energy bound strong enough to restart
(10)-(11) at multiple scales. The finite controls
already show many budget stops; they do not
support dropping this remaining population.
No unbounded favorable-reset construction,
twin-infinitude contradiction or Lean verification.
No canonical Lean target or sibling branch changed.
