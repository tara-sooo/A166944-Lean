# Negative MIN: compatible return capacity and short-repeat exclusion

2026-11-27 JST. Continuation of 13fa7a5c6d9b1ed6e358c9184038233e61d7ee36.
We isolate two mechanisms after a prime has first been used. The compatible
target lattice gives an unconditional bound on the entire label mixing with
already-used lower-label cohorts at the macroscopic end of the gain range,
without assuming a subpower-log event-count bound. At the very top of that
range only a plus-to-three bridge can contribute; simultaneous occupancy
of its block by a minus-p arrival forces a long stationary gap. Separately
we show that short p-q-p relays of macroscopic primes can be discarded from
actual low-gain slabs at a subleading entropy cost, using only a two-prime
CRT count and the elementary Chebyshev upper bound for prime counts.
No proof of the global event-count or entropy coefficient is obtained.
Paper-level deductions, not Lean verification or a priority claim.

## 1. Compatible target lattice, exact capacity

Use the selected slab of 589743f and 13fa7a5:
A in [R,2R], 6|A, K=floor(sqrt(R)/log^B R),
T=4K, J=floor(g T), fixed 0<g<2/9.
The selected set S consists of roots with G_T<=J.
Use their common postheight H=floor(3+T-J/2),
so all completed jumps are represented and the final
position equals the retirement position for large R.
Every jump decreases even position a by the positive
even number p-1.

Fix p>=5 used on one such path. Write sigma for its
first firing sign, g_p for pre-first gain, a_* for
its post-first position, and D=G_T-g_p-(p-1)>=0
for remaining gain. Let n_p be its total uses.
The post-p pin is a_*=0 mod p for minus, 2 mod p
for plus. As a_* is even, these are also exactly
the residue classes 0 and 2 mod 2p.
Every subsequent p-compatible arrival (any jump
ending at a=0 or 2 mod p) is at a distinct
position strictly below a_* within distance D.
The eligible positions occur alternately at
gaps 2 and 2p-2. Hence there are exactly

    C_p(D,sigma) = 2 floor(D/(2p))
                 + 1{D mod 2p >= l_sigma},
    l_+=2, l_-=2p-2,                            (1)

compatible positions in this interval.
Each subsequent p firing itself occupies one
of these positions. Let B_p^1(path) be the
number of later entries by labels q<p at
p-compatible positions, and let B_all count
all compatible arrivals after first p.
Then

    B_all <= C_p(D,sigma),
    B_p^1(path)+(n_p-1) <= C_p(D,sigma)
                                <= D/p+1.      (2)

This is not a condition on clocks, so it
bounds the number across all physical
blocks and applies to arbitrary subcohorts,
including actual slabs. If the prime is
unused, define all of these quantities zero.
The exact integer capacity in (1) permits
replacing D by J-g_p-(p-1).
The bound does not require the intervals
associated with different p to be disjoint.

For complete CRT periods, the first-pin
enumeration of 13fa7a5 gives g_p and sigma
for every affordable first-use lift. Thus
(1)-(2) provide a one-deleted-path statistic
for an upper bound on the used lower-label
mass before a gain-capped common height,
without enumerating post-first-p tails:
take E_- sum over affordable pins of
C_p(J-g_p-(p-1),sigma)/p. One can subtract
the actual repeat mean if independently
known. For a selected success cohort divide
by its fraction s. Exact equality does not
hold in general since most compatible
positions are skipped by actual jumps.

## 2. Unconditional macroscopic used-mixing entropy bound

At block v use the notation of 13fa7a5:
M_p=F_p+R_p is all entry mass of label p,
B_p=B_p^0+B_p^1 all smaller-label entry
mass, partitioned by whether p has been
used. For B_p^i restrict to compatible
positions since only those can have M_p>0.
The ordered label entropy telescopes
exactly into sum_p Phi(M_p,B_p), where

    Phi(x,y)=(x+y)log(x+y)-x log x-y log y.

Subadditivity separately in x and y gives
a slightly different split from the last
note:

    Phi(M_p,B_p) <= Phi(F_p,B_p^0)
                     + Phi(R_p,B_p^0)
                     + Phi(M_p,B_p^1).          (3)

The final term charges ALL p-used lower
entries together, including mixing with
repeated p arrivals. It is convenient to
treat it as a single term instead of
charging it to both first and repeat.

Take Y>=5 and let
m_Y=E_S sum_(p>=Y) N_p,
b_Y=E_S sum_(p>=Y) B_p^1(path).
The gain cap and (2) imply

    m_Y <= J/(Y-1),
    b_Y <= (1+J/Y) E_S #{used p>=Y}
         <= (1+J/Y) m_Y.

Using homogeneity and concavity of Phi,
the normalized sum of the used terms in
(3) for p>=Y obeys

    U_Y <= Phi(m_Y,b_Y)
         <= m_Y [1+log(2+J/Y)]
         <= J/(Y-1) [1+log(2+J/Y)].            (4)

For the middle inequality use
Phi(x,y)=x g(y/x) and
g(t)<=1+log(1+t). Zero mass costs zero.
Consequently U_Y=O_c(1) for Y>=cJ, fixed
c>0. For Y=J/L0, L0>=1 with
L0 log(2+L0)=o(loglog R), it is
o(loglog R). No mean event-count
hypothesis, large-sieve transfer,
maximum mass or independence is
needed for (4). It holds on actual
selected slabs.

This removes the already-used part
of the large-label entropy without
the previous conditional mean-count
bound. It does not remove the
first/virgin and repeat/virgin
terms of (3), or the used terms for
labels much smaller than J.
The earlier estimate of all
macroscopic high/low mixing still
requires a mean event-count bound.

## 3. At the top of the budget, only a plus-to-three bridge

Suppose p>J/3+1. Repeat spacing of 13fa7a5
gives N_p<=1. Also D<=J-(p-1)<2p-2.
The compatible lattice (1) has no positive
return after a first minus p, and at most
one after a plus p, at displacement 2.
Every jump costs at least 2, so the latter
is possible only if the very next jump
after plus p is label 3. It reaches
a=0 mod p. This proves

    B_p^1(path) <=
      1{first p is plus and next completed label is 3}.

In fact equality holds under this budget.
A used lower-label entry can therefore
mix with a first-p arrival in the same
physical block only in this specific
bridge configuration.

The plus source is a+p+1, its p jump
lands at a+2, and its following 3 jump
lands at a. A minus-p source for the
same block is a+p-1. The two source
positions differ by 2. Let n_+ be the
plus firing absolute time, n_3=n_++w
the 3 firing time, 1<=w<=6, and n_-
the minus-p arrival time. Then

    n_+ == p+2 mod 2p, n_- == 0 mod 2p,
    |n_3-n_-| >= p-8.                          (5)

For p<=8 the inequality is vacuous.
For larger p it follows from distance
to the nearest multiple of 2p.
If these arrivals are in the same
stationary block, their time difference
is strictly below 2q(a), where q(a) is
the least odd factor of a-1 or a+1:
the block cannot cross a firing clock
at its unchanged position, even when
truncated at the common height.
It follows that

    q(a) > (p-8)/2.

Thus the only top-band used-mixing
configuration is at a p-divisible
target with both neighbors rough
at a scale comparable to p. We
do not infer rarity of ROOT MASS
from rarity of such target positions.
The latter would still require
an incidence or mass estimate.

## 4. Short repeat p-q-p and actual root count

Assume J comparable to sqrt(R)/log^B R
with B>0 fixed, and Y=cJ, c>0 fixed
(up to integer rounding). Mark all
jumps with label >=Y as macroscopic.
Consider three consecutive marks p,q,p
with distinct p,q and with total gain
d_1+d_2<=D0 from all unmarked events
between the marks. Here d_1,d_2 are
even, and D0 can be fixed or growing.
The first and third p have signs
sigma,tau, and q has sign eta.
Write a for the source of the
first p. The intervening total gain
between these two p jumps is

    E=q-1+d_1+d_2.
    E == sigma+1-tau mod p.

Since E is even and sigma+1-tau
belongs to {-1,1,3}, there is
a positive odd integer k such that

    q = k p + sigma+2-tau-d_1-d_2.              (6)

Here p,q<=J+1 and the whole motif
costs 2(p-1)+(q-1)+d_1+d_2<=J.
In particular k=O_c(1). For a
single dyadic band [Y,2Y] and
D0=o(Y), k=1 for sufficiently
large Y; more generally (6) is a
bounded list of affine relations.
The first two spatial pins require

    a == sigma mod p,
    a-(p-1)-d_1 == eta mod q.                  (7)

For fixed p,q,d_1 and signs this
is a single even progression modulo
2pq. A source in the expanded slab
[R-J,2R] therefore has at most
O(R/Y^2+1) possibilities. Every
canonical root that reaches that
source is in [a,a+J], with at most
1+floor(J/6) possibilities, even
if arbitrarily many paths have
merged at a. This direct count
does not need a bound on endpoint
multiplicity, clock multiplicity
or conditional prime independence.

For each of O((D0+1)^2) ordered
gap pairs, 8 sign triples and
O_c(1) k, choosing p determines q.
The elementary upper prime count
pi(J+1)=O(J/log J) bounds the
number of choices. We obtain

    # canonical roots in [R,2R]
        with G_T<=J and such a motif
       <<_c (D0+1)^2 (R/Y^2+1)
                             J^2/log J
       <<_c (D0+1)^2 R/log R.                  (8)

The second line uses Y=cJ,
J^2=O(R), log J asymptotic to
(1/2)log R. This estimate uses
only the upper prime-count bound,
NOT a twin-prime or prime-pair
asymptotic. No external literature
search or new literature claim
is needed for the elementary
CRT argument. A standard fixed
nonzero affine two-prime upper
sieve could sharpen (8) for
fixed D0 by another log, but
the conclusions here use only
(8) and no such sharpening.

In particular for fixed D0 the
exceptional fraction among ALL
canonical slab roots is O(1/log R).
For D0=o(sqrt(log R)) it is o(1).
For a selected fraction s_R
the fraction within the selected
set is at most
O_c((D0+1)^2/(s_R log R)).
The bound is useful when the
selected fraction is not too
small. At finite R the constants
can be large: the exact raw CRT
union bound in the audit often
exceeds the slab population,
so it is an asymptotic bound,
not a numerically sharp estimate.

If the low gaps between marked
events use only a fixed alphabet
P_z, their gain is bounded by
the earlier finite spatial wall
for each such run. Thus (8)
also discards this class without
a separate numerical gap limit.
In particular any repeating
macro sequence with at most two
distinct macro labels and
bounded low gains between every
consecutive mark has a p-q-p
or q-p-q motif (adjacent equal
marks are impossible when their
intervening gain is <Y-1).
This is not an exclusion of
long repeat relays involving
three or more macroscopic labels,
nor of relays with a large
total unmarked gain.

## 5. Entropy cost of excluding those roots

For a selected cohort S let B be
the subset with one or more short
motifs above, eps=|B|/|S|, S0=S\B.
Conditional on endpoint a_T the
initial A lies in [a_T,a_T+J],
with at most 1+floor(J/6) possible
canonical roots. Let L(S) denote
the entropy loss H(A|a_T) for a
uniform root from S. The binary
partition gives exactly

    L(S) = H(1_B|a_T)
                      +(1-eps)L(S0)+eps L(B).

Hence

    0 <= L(S)-(1-eps)L(S0)
             <= h_2(eps)+eps log(1+floor(J/6)). (9)

Empty-cohort terms are omitted.
If s_R is bounded below and D0
fixed, (8)-(9) give O(1) extra
entropy and an o(1) change in
selected fraction. Since
loglog R tends to infinity,
this particular repeat class
can be discarded at subleading
cost even if its roots have
large endpoint multiplicity.
For growing D0 with
(D0+1)^2=o(loglog R), the extra
cost is still o(loglog R)
when s_R is bounded below.
Alternatively to seek merely
a sufficient good SUBcohort,
it suffices that eps=o(1) and
its own entropy satisfy the
frontier criterion; no need
to add the discarded cost.
Neither (8) nor (9) assumes
the frontier entropy criterion
already holds.

The new reduction is narrow
but unconditional on the
actual low-gain population:
in the macroscopic repeat
analysis we can focus on
relays with more intervening
marks or unbounded low gain.
For the upper entropy terms,
the used mass of macro labels
is subleading by (4) whether
or not a short relay occurs.

## 6. Reproducible audit

research/min_local_negative_compatible_return_short_relay_audit.mjs
commit 4ae020822b6752837fc19907a51fb806eb62cc22
blob c955d47b509fff84ee91b149611a68eed066759a

All canonical roots in six actual
slabs R=12000,48000,192000,480000,
1000000,2000000; K=floor(sqrt R/sqrt(log R)),
T=4K, J=floor(T/5). For each selected
root, record first use and all
compatible subsequent arrivals,
and verify (1)-(2). Check the
top-band bridge classification
and matched clock separation.
Use Y=max(5,ceil(J/8)), D0=0,4,8,16,
count the macroscopic repeats and
short motifs. Independently enumerate
all CRT candidate source progressions
from (6)-(7), with exact remaining
gain budget and canonical root counts;
verify upper bound on observed
keys and roots. Verify the entropy
partition (9) directly by endpoint
counts and used-mass estimate (4).

    canonical roots                    622004
    full completed events            14181783
    selected roots                     207261
    compatible capacity checks         659625
    top-band used return checks          7004
    one-intervening-mark congruences       718
    occupied top-band bridge mix checks     1
    aggregate macroscopic bound checks      6
    entropy partitions / CRT bounds     24 / 24

At R=2000000, N_s=115899, J=296,
Y=37: total mean event count 8.05027.
Mean used lower-label incidences
(all p>=5) 2.93097; capacity bound
25.50729. For macro p>=37:
mean p entries .66049750,
used lower entries .18548046,
compatible used bound .58623457.
Actual used lower label mixing
(sum Phi(M_p,B_p^1)/N_s) .00136890,
aggregate upper using actual
traffic .44494783.
Top-band first-use incidence
.14423766; used lower entries
.03495285, all plus-to-three
bridges, none at a block with a
first minus-p arrival of the
same label. The only occupied
bridge mixture across the six
slabs was at R=192000; (5)
was verified there. This small
count is not a universal zero
claim.

Mean macroscopic repeats .00893882;
with exactly one intervening macro
mark .00220019; of these short
with D0<=16 .00065574.
The remainder of the macro repeats
includes adjacent equal macro marks
with long unmarked gain and more
than one intervening macro mark.

    R       roots with D0<=16 motif   selected roots
      12000              28                 486
      48000              46                2080
     192000              66                8952
     480000              68               24664
    1000000              87               55180
    2000000              76              115899

For R=2000000:
D0=4: 7 roots, D0=8: 31 roots,
D0=16: 76 roots (23 distinct observed
spatial/sign/gap keys, 18 ordered
prime pairs). The D0=16 actual
discarded entropy component in (9)
is .00270741, upper .00802724.
The crude independent CRT union
count is 11793246 with 691840
candidate keys (multiplicity over
patterns), deliberately not a
sharp finite population bound.
All assertions passed. Script
executed in ECMAScript research
runtime, fetched at the exact
remote commit and re-executed with
matching output. Reproduce with
node. No separate Lean or Node run.

## 7. Remaining proof problem

The macroscopic used lower-label
entropy can be removed with no
mean-event hypothesis, and the
short two-label repeat class is
sparse on actual slabs, not just
on the formal CRT period. The
compatible-lattice bound for small
p remains very loose, as the audit
shows. The next substantial problem
is to estimate first/virgin and
repeat/virgin terms after many
small-label jumps, or to control
intermediate and small labels via
a fixed-alphabet run renewal whose
cost does not scale like J/p.
The selected mass lower bound,
full entropy coefficient <3,
formal-to-actual transfer, and
twin-infinitude proof remain open.
No Lean verification, canonical
target, sibling branch or Context
changes.
