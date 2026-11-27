# Negative MIN: soft roughness frontier and synchronized all-root occupation entropy

2026-11-27 JST. Continuation of 54567a9bf59f9a960f6fe33183bba5d7fc82330e.
The user asked to concentrate on the central asymptotic condition for
twin infinitude. We change the endpoint test from a hard near-square-root
roughness threshold to a weighted upper sieve over all roughness scales.
This gives a soft entropy criterion and, using common absolute-time
retirement in short birth windows, an all-root sufficient condition
without a separate low-gain selected fraction. A random observation
time has a roughness-deficit tail bounded by the logarithm of the event
count. This avoids charging the time index of an adaptive stop. Two
actual-integer audits are provided. The remaining entropy and count
asymptotics are not proved. Paper-level deductions, no Lean verification.

## 1. Weighted capacity of non-twin centers

Fix a constant C>0, let R tend to infinity, and use even centers
a in I_R=[R-C sqrt(R)-C,2R]. All relevant integers are positive
and a+/-1>1 for large R. Set

    S=sqrt(2R+1), L=log S,
    q(a)=min(least prime factor(a-1),least prime factor(a+1)),
    q_*(a)=min(q(a),S), d(a)=log(S/q_*(a)),
    w(a)=(log q_*(a)/L)^2 /
                  [(1+d(a))(1+log(1+d(a)))^2].

Define the penalty c(a)=-log w(a), namely

    c(a)=2 log(L/log q_*(a))+F(d(a)),
    F(d)=log(1+d)+2 log(1+log(1+d)).

Here F is increasing and concave on d>=0.
For large R all twin centers have q(a)>S and weight 1.
Every non-twin center has q(a)<=S.
We prove the uniform weighted capacity upper bound

    sum_(a in I_R, non-twin) w(a) <<_C R/log^3 R.       (1)

Use the two-dimensional upper sieve already applied in
d9f6049 and 74a6796; no new literature claim.
For every 3<=y<=R^theta, where theta=2/5 is fixed,
the number of even centers with q(a)>=y is
O(R/(log y)^2), with a uniform constant. For small
y use the usual upper sieve with level sqrt R; for
larger y sift only to min(y,R^epsilon), fixed small
epsilon, so the logarithmic bound still holds.
The two forbidden classes +/-1 modulo each odd
sieving prime are distinct. Prime powers or
exceptional zeros are not needed.

For q(a)<R^theta we have d(a) comparable to log R.
Then

    w(a) << (log q(a))^2 /
                       [log^3 R (loglog R)^2].

Split log q into intervals [2^j,2^(j+1)), j>=0.
On each interval the upper sieve just stated bounds
the count by O(R/2^(2j)); multiplying by the weight
bound gives O(R/[log^3 R (loglog R)^2]).
There are O(loglog R) such intervals. Therefore the
total small-q contribution is O(R/[log^3 R loglog R]).

For q(a)>=R^theta on the non-twin set, q(a)^3>2R+1,
so the composite neighbor is qr with primes q<=r,
and q=q(a) is the smallest factor of at least one
composite neighbor. This includes squares and both
neighbors composite. The other neighbor qr+/-2
has no prime factor below q. For fixed q and sign,
the fixed-factor upper sieve of d9f6049 gives
O(R/(q log^2 R)) centers. To verify uniformity:
r ranges in an interval of length O(R/q), sift r
and qr+/-2 by odd primes up to (R/q)^epsilon;
these primes are below q and r, the two forbidden
residues are distinct, CRT remainder is at most
2^omega(modulus), and the usual two-dimensional
upper sieve with level sqrt(R/q) has an absorbed
remainder O(sqrt(R/q) log(R/q)). Also log(R/q)
is comparable to log R. This is an upper sieve
only.

Split q into intervals (S exp(-(j+1)),S exp(-j)]
for nonnegative integers j, intersected with
[R^theta,S]. The Chebyshev upper prime count
gives sum of 1/q in each interval O(1/log R).
Indeed use the upper endpoint for prime count and
the lower endpoint for each reciprocal. On each
such interval the weight is at most

    1/[(1+j)(1+log(1+j))^2].

The series of these bounds converges by the
integral test. The total contribution is therefore
O(R/log^3 R), proving (1). This does not require
a lower bound for rough numbers at any scale.

The log-log factor in the weight denominator
is important at the critical exponent 1. One
can instead use (1+d)^(1+eta) for fixed eta>0;
the stated weight has a slightly smaller
large-deficit penalty. All logarithms are natural.

## 2. Soft frontier entropy criterion

For any nonempty cohort S_R of canonical roots
in [R,2R], 6|A, choose a center X(A) in I_R.
It may be the position at a fixed elapsed time,
a common height, a selected intermediate
position, or any deterministic function of A.
No synchronization or dynamics is needed for
this section. Put N=total canonical slab roots,
N_s=|S_R|, s=N_s/N, m(a)=# selected roots mapped
to a, and

    L_X = H(A|X) = (1/N_s) sum_a m(a)log m(a).

Since the root distribution is uniform,
by Jensen

    N_s exp(-L_X-E c(X))
           <= sum_(occupied a) w(a).                (2)

Indeed the average of w(X)/m(X) over roots is
the right side divided by N_s, and the mean
log of that ratio is -L_X-E c(X).
If no twin occurs in I_R, (1)-(2) imply

    L_X + E c(X) - log s >= 3 loglog R - O_C(1).      (3)

Thus if on unbounded slabs for fixed delta>0

    L_X + E c(X) - log s <= (3-delta) loglog R,       (4)

twin infinitude follows. More precisely, subtract
the capacity (1) from the left side of (2) to get
a lower bound on the number of distinct twin
centers occupied. Because twin weight is 1, an
unbounded excess proves infinitude.

For a hard near-square-root cohort q>=sqrt R/log^B R,
the penalty is O(logloglog R), so (4) recovers
the earlier entropy criterion up to subleading
terms. If q>=sqrt R exp(-(log R)^alpha), fixed
0<alpha<1, the penalty is at most
(alpha+o(1))loglog R. This wider roughness range
is allowed with a correspondingly stronger
entropy coefficient (<3-alpha).
The soft criterion also permits a mixed
population of centers across all scales.
For a fixed polynomial roughness q>=R^theta,
theta<1/2, the penalty can be about loglog R,
so the criterion does NOT bypass the sieve
parity obstruction at a fixed polynomial scale.

For a root code with weights k(A,a)>=0
such that sum_(A mapped to a) k(A,a)<=1,
the stronger direct certificate is

    sum_A k(A,X(A)) w(X(A))
                       <= sum_(occupied a) w(a).   (5)

In particular use the earlier reverse codes.
If multiple maps X_i with per-fiber codes k_i
are available, fix probabilities pi_i with
sum pi_i=1. For each root choose i(A) adaptively
and assign weight pi_i k_i(A,X_i(A)).
The per-endpoint sum is still at most 1,
since it is bounded by the mixture of the
full per-map sums. Thus neither adaptive
map choice nor multiple horizons requires
a new ancestry theorem if valid component
codes are already available. For exact
uniform fiber code k_i=1/m_i this also
gives an entropy upper bound by expected
-log(pi_i k_i). The audit checks (5)
for four maps and uniform mixture; it does
not claim that the mixture beats the best
map's certificate.

## 3. Synchronize all roots in short birth windows

Take T=ceil(S), W=6 floor(T/6). Partition the
canonical roots in [R,2R] into consecutive
windows of spatial width W, starting at the
smallest canonical root lo. For a window
with left boundary l, all its births have
absolute times 3-A/2. Its latest birth time
is n0=3-l/2. Observe all roots of this
window at common absolute retirement
n0+T. Their elapsed horizons belong to
[T,T+W/2), hence are <=1.5T.
Nonnegative height gives total gain
<=3T+6. For large R, physical negative
domain is maintained and every visited
center is in [R-3T-6,2R].

Write Y(A) for the synchronized retirement
position and N_e(A) for its completed
event count. Use the FULL uniform slab
population, no gain selection. Let
L_end=H(A|Y), M=E log(1+N_e).
For each integer 0<=u<T, let X_u(A)
be its position at absolute n0+u
(using the n0 of its own window).
These are all actual MIN positions.

Let J be window index. For any fixed u,
within each window the future from X_u
to Y is deterministic: they are actual
states at the same absolute tick.
Hence

    H(A|X_u,J) <= H(A|Y,J) <= H(A|Y).

Given X_u=a, every possible initial root
A is in [a,a+3T+6]. This interval
intersects at most
B0=ceil((3T+6)/W)+2 windows, bounded
by an absolute constant. Thus

    L_u=H(A|X_u)
        <= L_end + log B0.                         (6)

This proves uniform entropy control at
every observation offset, with no need
to record a distinct stopping time
for each root. It is important that
u is common in each birth window.
For unrelated elapsed horizons or
root-dependent chosen times, the
same monotone entropy argument does
not automatically hold.

## 4. Clock occupation gives a logarithmic-count roughness bound

For one root A, partition its T observed
post-tick states (absolute n0 through
n0+T-1) into stationary intervals.
There are at most N_e(A)+1 such intervals.
At position a, an eligible clock with
least label q(a) recurs every 2q(a)
ticks. The unchanged-position interval
contains at most 2q(a) post-tick states
before that clock or an earlier winner.
Truncation by the observation window
only decreases this count.

For U uniform on {0,...,T-1},
conditional on the entire root path,

    Pr_U(q(X_U) < z | A)
         <= min(1,2z(1+N_e(A))/T).                 (7)

In particular a longest stationary
interval has roughness at least
T/[2(1+N_e(A))], but choosing it
root by root would introduce a
clock-block ambiguity in entropy.
Use the common random offset instead.

Put b_A=log(2S(1+N_e(A))/T).
For large R, T=ceil S implies
0<=b_A<=log 2+log(1+N_e(A)).
For t>=0, (7) gives

    Pr_U(d(X_U)>b_A+t | A) <= exp(-t).

Integrate this tail:

    E_(A,U) d(X_U) <= 1+log 2+M = D.             (8)

For even centers q>=3. The function
2 log(L/(L-d)) is convex on
0<=d<=L-log 3, so is bounded above
by its chord through both endpoints:

    2 log(L/(L-d)) <= k_R d,
    k_R=2 log(L/log 3)/(L-log 3)
             =O(loglog R/log R).

The remaining penalty F(d) is
concave and increasing. By Jensen
and (8),

    E_(A,U) c(X_U) <= k_R D+F(D).                 (9)

There exists a deterministic common
offset u_R with mean penalty no
greater than (9). Combine (6) with
the soft criterion (4) at this
offset. We get a single all-root
sufficient condition:

    L_end + log B0 + k_R D + F(D)
                        <= (3-delta)loglog R       (10)

on unbounded R. No separate
positive selected fraction or
low total gain bound is required.
All statements in (6)-(10) hold
on actual integer slabs, not
on the formal CRT model.

For example if M=(log R)^{o(1)}
(the precise requirement is
log(1+M)=o(loglog R)), then the
extra penalty in (10) is
o(loglog R). This is much weaker
than requiring a subpower-log
mean event count: even a mean
event count log^C R implies
M<=log(1+E N_e)=O(loglog R).
More generally if
M<= (log R)^(alpha+o(1)),
0<=alpha<1, then
k_R D=o(1) when alpha<1 and
F(D)<=(alpha+o(1))loglog R.
So L_end <=(3-alpha-delta)loglog R
would suffice. These are conditional
asymptotic targets; neither the
entropy bound nor M bound is
proved. In particular even
removing selection from the
statement does not prove that
the all-root entropy is easier
to bound than the selected one.

The physical stationary-block
entropy ledger of 589743f applies
within each synchronized window,
with its common retirement in
place of the common height.
Across windows the final position
has O(1) additional window-index
entropy by the same gain cap.
This permits reuse of the
birth/label/time decompositions
for (10); no new all-root
incidence estimate is asserted.

## 5. Executed audits

Both final scripts executed in
the ECMAScript research runtime,
fetched at exact remote commits,
and re-executed with matching
outputs. Reproduce with node.
No separate Node/Lean invocation.

A. research/min_local_negative_soft_frontier_entropy_audit.mjs
commit 8dd18ebecab083eb83b22add64b0b5ea725b8785
blob c8c9cb786a6451b721800115a8bc3642c51fe140

Six actual slabs R=12000,48000,192000,480000,
1000000,2000000. For every canonical root
simulate T0=4 floor(sqrt R/sqrt(log R))
and U=ceil(8 sqrt(2R+1)), record seed,
both endpoints, best q visited through
each horizon, and the old low-gain
selected short endpoint. Enumerate
weighted non-twin capacity in the
entire expanded slab. Compare
Jensen lower bound (2), exact
weighted support, and the four-map
adaptive Kraft certificate (5).

    canonical roots               622004
    completed events             20088408
    center weights                1909849
    score checks                       42
    per-endpoint Kraft checks        33336
    adaptive root choices           622004

At R=2000000, N=333333,
T0=1484,U=16001.
Full expanded-slab non-twin
weighted capacity=3537.838275,
scaled by log^3 R/R=5.402437.
The six scaled capacities are
4.7382,5.0035,5.1867,5.2766,5.2571,5.4024.
These finite values are NOT
the constant in the asymptotic
upper bound (1).

    map              L_X       penalty    total incl -log s
    seed             0         6.01878       6.01878
    short endpoint   3.56220    .78118       4.34338
    short best       3.71615    .44972       4.16588
    long endpoint    4.26325    0            4.26325
    selected short   2.62110    .10106       3.77859
    adaptive code    3.90306    .15990       4.06296

All-root short best weighted
support=13233.422285, Jensen
lower bound=5172.033246,
both above finite non-twin
capacity. Uniform mixture code
certificate=3419.467046,
below finite capacity: the
actual adaptive mapping has a
better Jensen lower bound than
this particular code. The
explicit finite twin centers
are already present; these
checks do not establish
unbounded R or the asymptotic
coefficient. All assertions passed.

B. research/min_local_negative_synchronized_occupation_entropy_audit.mjs
commit 3ca2173fc08344b93d64f488d0b3257c6e4a9b2b
blob c76ddcedf3325086e00b555033292e58366f75b8

Same six slabs, all roots,
T=ceil(S), W=6 floor(T/6).
Compute actual occupation
lengths and mean deficit for
each root, check (7) at t=0,1,2,4
and (8) per root. Difference
array of weighted penalties
at every common offset gives
a minimizing u_R. Independently
replay all roots at that offset
and final retirement, check
the deterministic same-window
future and window ambiguity,
entropy and Jensen inequalities.

    roots                         622004
    completed events            17010526
    occupied interval segments   9730511
    per-root tail controls       2488016
    per-root mean controls        622004
    second full root replay       622004
    second completed events     17010526
    deterministic fiber checks    622004
    window ambiguity checks        29381

    R         mean events  E log(1+N_e)   L_end     mean deficit
      12000      10.5142       2.10086    2.49290      .92457
      48000      14.4997       2.36892    2.99246      .82736
     192000      19.9435       2.64587    3.38907      .77957
     480000      23.3300       2.76928    3.65900      .68783
    1000000      26.5271       2.87164    3.80766      .61816
    2000000      29.8430       2.97834    3.98902      .57103

At R=2000000:
T=2001,W=1998, u_R=1999.
L_end=3.9890164; conditional
within-window L_end=3.5773586.
L_u=3.9887933; within-window
L_u=3.5773024. Maximum observed
window ambiguity 4.
Mean penalty over offsets=.8672537,
minimum=.3647818; D=4.6714911,
upper penalty (9)=6.5272778.
The observed score is 4.3535751,
ratio to loglog R=1.6276595.
Jensen support=4286.913103,
finite bad capacity=3501.210442.
The analytic sufficient upper
score in (10) is 12.3080537
at this R, much larger than
the actual score. Thus the
universal bound is valid but
not numerically sharp; the
asymptotic route is not established
by these finite data.
All assertions passed.

## 6. Proof status and next priorities

The hard selected-cohort
criterion is no longer the
only route. The new soft
capacity uses the entire
range of q, and synchronized
clock occupation eliminates
the need for a separate
low-gain selection theorem.
The two all-root targets are
an entropy bound below the
coefficient 3 (with allowance
for the penalty) and a
sufficiently small logarithmic
event-count average M.
The second is weaker than
the old mean count condition,
but is not derived here.
The earlier small-alphabet
run walls, first-use deletion
and return capacities remain
relevant to both estimates.
Their formal-to-actual transfer
is not solved; (10) states the
needed conclusions directly on
actual slabs.
No twin-infinitude proof,
Lean verification, canonical
target, sibling branch or
Context changes.
