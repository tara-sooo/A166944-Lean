# Negative MIN: cohort transport, merger energy and high-wait mass

2026-11-26 JST. Continuation of 2021e5a7bd6ea7a79ecd2ef9b53eedef7dfb7b4d.
Develop an actual finite-slab cohort formulation at a fixed
linear elapsed horizon. Obtain an exact mass transport and
gain ledger, a necessary twin-basin concentration bound
for the proposed mean-gain target, an unconditional high-label
wait upper bound in terms of merger energy, and explicit
canonical many-parent mergers. The desired unconditional
mean-gain saving at linear horizon is NOT obtained.
Paper-level deductions and reproducible finite audit;
no Lean-verified theorem or twin-infinitude claim.

## 1. Cohorts and absolute-clock transport

Let R tend to infinity, N=#A_R, where
A_R={A in [R,2R] : 6|A}. Thus N=R/6+O(1).
Set T=floor(R/8), birth n_A=3-A/2,
retirement n_A+T, and common terminal time

    n_* = max_A(n_A+T)<0.

Until retirement there is no half-distance or time
boundary for large R: G_t<=2t+6, so a>=A-2T-6,
and all absolute times are negative. For the energy
ledger continue all roots (including retired roots)
under the ordinary dynamics until n_*. Negative-time
nonnegative height ensures all distances remain
positive up to that time. The retired roots are
retained only for coalescence bookkeeping; their
subsequent jumps do not count toward G_T.

At each absolute tick n define F_n(a) to be the
distance after the least-prime firing at that tick,
or a if none. For even n, eligible p divides n and
a+1; for odd n, p divides n-2 and a-1. Use absolute
values for negative divisibility. When p fires,
F_n(a)=a-p+1. This is deterministic at fixed n.
Define full mass M_n(a) of all born roots at a
after tick n (including the new birth if any).
Define active mass U_n(a) of roots still to retire
after that tick. Let B_n(a) be the birth indicator
for a canonical A at n_A=n and a=A.
Let D_n(a) count retirements at n at position a
after applying the tick and birth. Then

    M_n(b) = sum_(a:F_n(a)=b) M_(n-1)(a) + B_n(b),
    U_n(b) = sum_(a:F_n(a)=b) U_(n-1)(a)
                                  + B_n(b)-D_n(b).

Birth is after the tick and retirement is after the
tick; a birth does not receive that tick's event.
The exact cumulative gain ledger is

    sum_A G_T(A) =
      sum_n sum_a U_(n-1)(a) [a-F_n(a)].           (1)

It can also be checked by summing A-a at retirement.
No independence or uniformity of U_n is assumed.
If two roots reach the same distance at the same
absolute time, they have identical future states.
Equal positions at different elapsed times alone
are not a general coalescence condition.

Define full energy C_n=sum_a M_n(a)^2. It counts
ordered pairs of born roots at the same absolute
state, including the diagonal. Without births,

    C_n-C_(n-1)
     = 2 sum_b sum_(a<a',F_n(a)=F_n(a')=b)
                         M_(n-1)(a) M_(n-1)(a').

Birth of one root at b adds 1+2 times the mass
already there after the tick. Thus C_n is
nondecreasing. Put C=C_(n_*). This choice of full
energy avoids subtracting pairs at retirement.
It is not in general the squared mass sum at a
single *relative* elapsed horizon.

## 2. Twin absorption, residual idle time and mean gain

For each root let W_T be the sum of completed
event waits, I_T=T-W_T the unfinished idle duration,
and a_T=A-G_T the terminal distance. The mod-30
potential of 2021e5a yields W_T<=(9/4)G_T+8, hence

    E I_T >= T-(9/4) E G_T-8.                    (2)

If a_T is not a twin center, the next wait at its
last arrival is <=2sqrt(2R+1) by the least factor
bound. Therefore I_T<=2sqrt(2R+1). Write S=sqrt(2R+1).

If a is a twin center in this horizon, it has
a>=A-2T-6>A/2 for large R. Its previous plus
clock was 3-a, its next plus clock a+1, and
the minus clock nearest at or after arrival is 0.
The actual arrival time is at least 3-A/2>3-a.
Thus it is absorbing until tick 0, including all
remaining times through n_*. No twin source can
have a completed firing within the relative T
horizon. Any root at a twin terminal position
must therefore remain there through n_*.

Let B count roots whose a_T is a twin center,
and b_y their multiplicities at each twin y.
Define C_tw=sum_y b_y^2 and m_tw=#occupied
twin centers. We have

    E I_T <= T B/N + 2S(1-B/N),
    C_tw<=C,
    B^2<=m_tw C_tw.                              (3)

In particular, for T>2S,

    E G_T >= (4/9)[(T-2S)(1-B/N)-8].             (4)

The proposed mean criterion E G_T<=R/20 implies
B/N>=1/10-o(1). This is a NECESSARY consequence,
not an independent lower bound on B. More generally
a fixed proportional gap below R/18 implies a
positive fraction of all roots must be absorbed
by twin centers at the horizon. One isolated
polynomial-length idle episode is not enough
for the mean criterion.

All terminal centers lie in [3R/4-6,2R]. The
standard dimension-two upper sieve (same input
as the stationary sieve of 74a6796, or the
upper sieve of 9103219) gives an unconditional
upper bound O(R/(log R)^2) on the number of
twin centers in this interval. For completeness,
sift the two neighbor forms a-1,a+1 on the even
progression with odd primes up to R^epsilon
for a fixed small epsilon; the CRT remainder is
<=2^omega(d), the Euler product is O(log^-2 R),
and the level sqrt R remainder O(sqrt R log R)
is smaller than the main upper bound. Actual
twins at scale R survive all these small primes.
No lower sieve for twins is used.

Combining with (3), any mean gain saving of
fixed positive linear size below R/18 implies

    C/N >> (log R)^2.                            (5)

Conversely, if along a sequence C/N=o(log^2 R),
then B/N=o(1) by (3), and (4) implies

    E G_T >= R/18-o(R).

Thus a successful mean-gain argument necessarily
has substantial mass concentration on the actual
twin centers. A model that treats the ensemble as
having bounded multiplicity cannot produce the
proposed saving. This is a necessary structural
condition, not a way to infer absorption from
large full energy alone.

There is also a geometric constraint on each
twin basin. The b_y roots A are distinct multiples
of six with A>=y and G_T(A)=A-y. Therefore

    sum_(A:a_T=y) G_T(A) >= 3 b_y(b_y-1).

Sum over y and combine with the pointwise mod-30
bound for non-twin terminal roots:

    sum_A G_T(A) >=
         (4/9)(T-2S-8)(N-B) + 3(C_tw-B).         (6)

A sharper variant retains the individual basin
offsets rather than only b_y. In particular, if
E G_T=o(R), (4) forces B/N->1 and the basin term
forces m_tw >> R/(E G_T+1). These implications
do not yield any unconditional upper bound on
E G_T.

## 3. Unweighted efficient high-clock capacity on a physical slab

The common-time ledger permits a sieve bound on
distinct physical firing keys (a,n), rather than
on ordered words from the canonical root. Each
such key has one winning label p and side e.
Different roots sharing this firing can have
different waiting times (different arrival times).
Only count incidences completed by their own
retirement. Let m_e be their multiplicity.
For every key all roots sharing it have coalesced
by that tick, hence belong to one full final
cluster of size >=m_e.

Choose Y sufficiently large, Y<=R, and call
p>=Y high. Put delta=1/(log Y)^2. A high
incidence is efficient when w>=delta(p-1).
Inefficient high incidences contribute at most

    delta sum_A G_T(A) << R^2/(log Y)^2            (7)

to the total waiting time, by G_T<=2T+6.
All completed events have non-twin sources, so
w<=2 min(p,S). For an efficient event this
also gives p<=1+2S/delta=O(sqrt R log^2 R).

An efficient physical key must have p|a-e,
and every odd prime q<delta(p-1)/2 divides
neither a-1 nor a+1. Otherwise its clock
would fire before the actual event, since its
wait is <=2q. At each p and fixed side,
a is one even residue class mod 2p within
[3R/4-6,2R], whose progression parameter
has length O(R/p) and comparable to R/p.
For q distinct from p, the two prohibited
residues are distinct modulo odd q. Sift
on primes up to the smaller of
delta(p-1)/4 and (R/p)^(1/10). For sufficiently
large Y,R this cutoff has logarithm comparable
to log p, uniformly on the efficient range
p<=O(sqrt R log^2 R): delta>=1/log^2 p and
R/p is at least a fixed positive power of p.
The elementary dimension-two upper sieve
with level sqrt(R/p) therefore gives

    # eligible rough a << R/(p log^2 p).         (8)

The CRT remainder is <=2^omega(d) as in
74a6796; the summed sqrt(R/p) log(R/p)
remainder is absorbed uniformly in (8).
The same fixed constants work for all p
in the efficient range; p itself is absent
from the smaller sieve cutoff. This estimate
uses a necessary spatial roughness condition,
not a distribution assumption on actual
selected positions or path multiplicities.

The absolute firing times of the specified
side are in a single class mod 2p in an
interval of length O(R), so there are
O(R/p) possible times. Assign capacity

    b_e=2 min(p,S)

to a distinct physical key containing at
least one efficient incidence. By (8), summing
the capacity over all such keys gives

    K_Y=sum_e b_e
       << R^2 sum_(p>=Y) 1/(p log^2 p)
       << R^2/(log Y)^2.                         (9)

The last estimate follows by Chebyshev's
prime-count upper bound and dyadic summation,
or partial summation. Notice the additional
log from summing only primes. All side
constants are absorbed. No finite-interval
CRT product over an adaptive word appears.

This is an unconditional bound for the
unweighted capacity of distinct physical
keys at the actual linear horizon. It does
NOT by itself bound the mass-weighted wait:
a single physical key may be used by many roots.

## 4. Convert key capacity to weighted waiting via energy

Let L_e be the sum of efficient waits of
the roots sharing key e. By Cauchy-Schwarz
and w<=b_e,

    L_e^2/b_e <= m_e sum_(efficient roots at e) w.

Each root appearing at any such key belongs
to a common final cluster of size c(A)>=m_e,
and its total completed wait is <=T. Thus

    sum_e L_e^2/b_e <= T sum_A c(A)=T C.

A second Cauchy-Schwarz and (7)-(9) give

    sum_A W_(p>=Y)(A)
       << R^2/(log Y)^2 + R sqrt(T C)/log Y.

Equivalently the per-root mean high-label
completed wait satisfies

    E W_(p>=Y)
       << R/(log Y)^2 + R sqrt(C/N)/log Y.        (10)

All constants absolute for sufficiently large
Y,R, with T=floor(R/8) and N~R/6. Another
form does not require a bound on full energy:
for efficient keys with m_e<=M, L_e<=M b_e.
Including all inefficient high waits gives

    E W_(p>=Y, m_e<=M)
          << R (M+1)/(log Y)^2.                  (11)

These are nontrivial unconditional linear-horizon
upper bounds for COMPONENTS of the waiting ledger,
not for total gain. In particular if Y->infinity
and M=o(log^2 Y), the contribution of high clocks
at light-mass keys is o(R) per root, even if
the heavy clusters elsewhere are arbitrarily
large. A macroscopic high-clock wait must
then occur at larger multiplicities. The
energy criterion (5) explains why just setting
C/N=O(1) in (10) does not give the desired
mean-gain conclusion. Also, (10) controls
WAIT, not high gain; a large jump with small
wait can contribute little to (10) and much
to G_T. Small and middle labels and the
root-mass-weighted terminal gains remain
uncontrolled in general.

## 5. Canonical many-parent mergers, not only abstract collision mass

Fix an integer r>=1. Choose r distinct primes
p_i from a band [Y,2Y), all p_i=1 mod L,
where L is a fixed multiple of 12 and all
odd primes <=2(r+1). For every fixed r
such a choice exists for large Y by PNT
in a fixed progression (same standard
input as 2021e5a). Take a target canonical
B=0 mod12 and impose B=2 mod p_i for every i,
and B=0 mod the other small fixed primes.
For each parent

    A_i=B+p_i-1

we have 6|A_i, and the plus p_i clock
would fire at the exact canonical birth
time n_B=3-B/2 of target B. Indeed A_i=1
mod p_i, n_B=2 mod p_i and n_B is odd,
so n_B=p_i+2 mod 2p_i. The waiting time
from its own birth is (p_i-1)/2, and the
previous p_i clock is before birth. Thus
if not preempted the jump lands at B at
its birth time with height 3.

At other selected primes p_j, parent
A_i= p_i+1 mod p_j. Eligibility would
require p_i=0 or -2 mod p_j; neither is
possible for distinct primes in the
same factor-two band with both =1 mod6.
At B the selected primes are ineligible.
Small fixed primes are ineligible at all
these states because B=0 and p_i=1
mod each of them. In particular 3 is
ineligible throughout the stationary
pieces.

Choose K>2Y and require that every free
odd prime through z=2K+7 divide neither
neighbor of B nor either neighbor of
any parent. Each free prime prohibits
at most 2(r+1) residues of B, fewer
than that prime. All local constraints
are compatible. The height-local clock
cutoff ensures no larger prime can
preempt the selected event or the
terminal idle tail: during initial
waiting all heights are <=3+K and
during the tail they start again at 3.
Thus all r parents merge into B
exactly at its birth, and B and all
parents are stationary there for
the following K ticks. This supplies
a (r+1)-fold merger without assuming
anything about twin primality of B.

First, keep p_i and K fixed. The
positive and negative conditions
can be realized by a single actual
residue class of B modulo a finite
product (choose one surviving
residue at each free prime and CRT).
Consequently there is a positive
density, depending on r and the
chosen constants, of actual B in
[R,3R/2] satisfying this pattern for
all sufficiently large R. The parents
lie in [R,2R]. Star root sets for
different centers are disjoint: a
parent has a unique first event and
its destination; a center has no
event through K, whereas every parent
fires by Y. All sets are merged
by the common terminal time n_*.
In particular for every fixed r
some positive fraction of the slab
roots belongs to clusters of size
>=r+1 at n_*, unconditionally.
This fraction depends on r and
may be very small. It is not a
uniform bound as r grows, and the
stars are not asserted to absorb
at twins.

Second, let Y=R^alpha, K=floor(R^eta)
for fixed sufficiently small 0<alpha<eta
depending on r, r alpha<1/4.
The positive modulus for B is
O_r(Y^r). The roughness sieve now
uses dimension 2(r+1) and cutoff
O(R^eta). Its hypotheses and
remainder estimates are exactly
the bounded-dimension progression
sieve of 2021e5a. Choose eta small
enough that its lower main term
is positive uniformly, then alpha
smaller. Each compatible prime
choice gives >> R/(Y^r log^(2r+2) R)
centers in [R,3R/2]. There are
>> (Y/log Y)^r unordered choices
for fixed r, with the constant
including r!. A center B may be
counted repeatedly, but every
selected prime divides B-2,
so at most log(2R)/log Y=O_alpha(1)
such primes are available. This
bounds the number of choices per
center by a fixed constant.
Consequently

    # centers >>_(r,alpha,eta)
                     R/(log R)^(3r+2).           (12)

Their parent sets can be chosen
disjoint for the same reason as
above. Each has r+1 roots merged
by an elapsed time O_r(Y), then
an idle segment of length K. In
particular these contribute
Omega(R/log^(3r+2) R) distinct
ordered coalesced pairs beyond
the diagonal at the linear common
terminal time, with constants
depending on r. No large-gain
control after the idle segment is
obtained. All roots are actual
physical slab roots in (12), not
enormous formal CRT representatives.

The exact restart identity for
a parent holds at any elapsed
horizon t >= (p_i-1)/2 before
the physical boundaries:

    G_t(A_i)=(p_i-1)+G_(t-(p_i-1)/2)(B).

This illustrates why merging can
propagate a favorable future gain
from one center to multiple roots,
but does not make the center
favorable by itself.

## 6. Executed audit and independent sweep

Source research/min_local_negative_cohort_energy_audit.mjs,
commit c404c967a52c50f80905774a98ef2ea7dad800ec,
blob 463209cf4f774f322256ad5812463bcc3e6ede44.
Executed in ECMAScript research runtime,
fetched at exact commit and re-executed
with identical output. Reproduce with node
on the source. No separate Node or Lean run.

Five slabs, all canonical roots and T=floor(R/8).
Compute ordinary event paths separately for each
root to retirement, then continue to common n_*.
Record physical event keys and incidence waits;
check full cluster consistency, terminal absorption,
(3), (6), exact finite spatial/time key caps,
and the two weighted Cauchy-Schwarz inequalities.

    roots                             122505
    completed incidence events       3261887
    additional common-time events         234
    distinct active event keys        357657
    event mass checks                 357657
    terminal checks                   122505
    efficient roughness checks        219578
    finite CRT key capacity checks      4477
    high-cut/energy inequalities          25

Independent common-clock transport:
maintain full and active cluster masses, event
buckets, and union-find memberships. Process
all events at a tick simultaneously, births
after events, retirements after births. Count
active mass times jump gain and independently
sum gains at retirements. Recompute energy
from the final cluster masses and from each
merger's increment 2mn plus birth increments.
All totals match the individual trajectories.

    sweep moves                       357657
    retirements                       122505
    birth merges                       53984
    event merges                       62715
    total merge checks                116699
    full energy/ledger comparisons          5

In these particular slabs the extra common-time
events were already among the active physical
keys of other roots; equality of the two key
counts is not a general theorem.

    R       mean G_T/R   twin fraction   C/N       max cluster
    3000     .04759148       .964072     18.2136       42
    12000    .01625737      1            31.6447       81
    48000    .00817732      1            46.9465      143
    192000   .00376611      1            75.5890      309
    480000   .00189404      1            89.0612      432

All these finite slabs satisfy the mean target
R/20, and the table directly shows why: most or
all roots have already reached actual twins.
This is not a test of the hypothetical finite
twins regime. No extrapolation of the table
to an asymptotic gain law is claimed.

For the star structure independently enumerate
60668 canonical targets B divisible by 12
in four slabs R=12000,48000,192000,480000,
with B<=2R-1000. Inspect prime divisors
p of B-2 with p=1 mod6 and p<=2sqrt R.
Direct first-event simulation verifies 15890
successful parent returns. At R=480000 the
39917 targets include 9502 with at least one
parent, 899 with exactly two, 46 with exactly
three, one with four. These are direct stars
without the extra target idle constraint.

Four additional constructed complete residue
environments (r=1,2,3,4) include target idle
tails, 16236 prime checks, 430354 tick checks.
E.g. r=4 selects 20161,21001,21841,24781,
target idle K=49562. Formal tick simulation
matches the specified r direct parents and
target exactly. The huge CRT representatives
are not materialized; actual polynomial-scale
slab existence follows from the mathematical
sieve in section 5, not this simulation.

All final finite assertions passed. No
numerical optimization of implicit constants
or formal Lean check. The asymptotic sieve
inputs are the same established inputs as
the earlier notes; the new deductions do not
claim literature priority.

## 7. Status and next bottleneck

The equal-elapsed mean-gain problem now has
an exact mass-weighted ledger at linear time.
Large-label efficient distinct-key capacity
is o(R^2) as Y grows, and the bounds (10)-(11)
identify the amplification that can arise
from coalescence. Canonical stars supply
actual unconditional examples and fixed-r
positive-density merger classes. The desired
unconditional upper bound E G_T<R/18 has
NOT been derived. Neither many-parent mergers
nor energy growth alone imply that their
descendants have small cumulative gain.
In particular (5) is necessary, not sufficient.
The missing estimate concerns joint evolution
of cluster size, descendant gain and terminal
idle time, with the low/middle labels also
included. No proof of twin infinitude, no
Lean verification, and no changes to canonical
Lean targets or sibling branches.
