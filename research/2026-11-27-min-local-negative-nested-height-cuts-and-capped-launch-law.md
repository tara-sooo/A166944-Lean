# Negative MIN: nested preheight cuts, fresh-prime lift, and height-capped launch law

2026-11-27 JST. Continuation of 828a62e79e05201eb04b885c5a7fb70867b68de2.
The previous gain-threshold cuts were not nested, and almost all
future-top-slow pruned first mergers occurred at small-label arrivals.
Here we use first PREheight cuts, which ARE nested on common survivors.
There is an exact physical pair interval identity and one-level
pushforward with a fresh-prime dilution identity. A height cap (rather
than a small gain cap) permits full finite-alphabet absorption profiles,
including long low-height histories with polynomial wall bounds.
This gives weighted actual launch estimates at a logarithmic height
cap and a stopped-gain o(T) theorem for these histories. The new cuts
also account for a large fraction of the finite future-top-slow pair
energy. The energy increment after a moving cut and the recycled
high-height histories remain uncontrolled. No twin-infinitude proof,
Lean verification, or claim of literature priority.

## 1. First preheight cuts and deterministic locality

Use actual canonical roots A in [R,2R], 6|A,
initial position a=A, absolute tick n_A=3-A/2,
height h=3. Horizon T=ceil(8 sqrt(2R+1)).
At a tick n, let its PREheight be b=n+a/2
where a is the position immediately before
the tick. If a label p fires, postheight is
b-(p-1)/2; otherwise it is b. The preheight
at the next tick is at most b+1. The tick
rule permits labels dividing 2b+1 at even n
and 2b-5 at odd n. Hence at b<=H all eligible
labels are <=2H+1. These statements are used
only in the physical nonnegative-height region
or its finite congruence extension.

For integer H>=3 define the cut C_H as the first
tick with PREheight H+1, recording its source
position a and absolute tick n=H+1-a/2. Thus
all completed events strictly before C_H have
preheight <=H. This is deliberately distinct
from the first POSTheight convention in earlier
notes and from an elapsed-time or gain cut.
The root may fire at the cut tick itself; the
cut is taken BEFORE that firing. If not reached
by T, the cut is censored.

Let P_H be all odd primes <=2H+1,
Q_H their product, and M_H=2 Q_H/3. The
restricted finite-alphabet process is spatially
periodic under a->a+2Q_H and has walls at
a/2 divisible by Q_H (0116e3e). In particular
starting at any even a, the total gain before
absorption is <=D_H=2(Q_H-1).
For canonical roots translation A->A+6M_H
changes n_A by -3M_H, preserving all low
coordinates and parity. A restricted prefix
through the first preheight H+1 matches the
full rule tick for tick, because no larger
label can affect any earlier tick. The wall
guarantees that the restricted cut is attained:
either a future event reaches this preheight,
or a terminal idle run does. If its source
is a and gain is G=A-a, its elapsed cut time is

    t_H=H-2+G/2 <= H-2+Q_H.                    (1)

This follows directly from n=H+1-a/2 and n_A.
In the formal congruence extension the same
formula holds. On actual slabs it is valid
whenever the cut fits the physical horizon.
By the Chebyshev prime-product bound, for
H<=c log R with c a sufficiently small absolute
constant, Q_H<=R^u (e.g. u=1/100) and every
root in a sufficiently large slab attains C_H
well before T. The cut may include arbitrarily
many low-height events up to the wall budget,
without the polylogarithmic gain cap of 939e39d.

## 2. Nested partitions and exact periodic moments

For H<K, suppose two roots share C_H and each
attains C_K by its own horizon. They then share
C_K: preheight increases by at most one, so
neither has attained the higher cut previously,
and after C_H their absolute-time futures are
identical until the earlier retirement.
Thus on the subset attaining C_K the lower-cut
partition refines the higher-cut partition.
Without a common survivor condition the total
energy need not be monotone (roots can retire).
For the uncensored formal congruence extension,
all cuts are attained by (1), and partitions
are nested without restriction.

Let f_H(a) count all formal canonical roots
on the infinite translated line having C_H
at a. By (1) each root lies in [a,a+D_H],
so this is finite. It is periodic modulo
6M_H. On a full spatial period (even a),

    sum f_H(a)=M_H,
    kappa_r(H)=(1/M_H) sum f_H(a)^r, r>=1.     (2)

For each canonical root residue there is
exactly one cut residue; the actual displacement
is bounded by D_H<6M_H, so no ambiguity arises
from multiple lifts of the same root class.
Alternatively count translation orbits of
the root-to-cut map. In particular kappa_1=1.
If H is increased, lift the old period to
the larger common period. The nested refinement
coalesces classes but never splits them.
Hence kappa_r(H) is nondecreasing in H
for all real r>=1, and kappa_r(H)<=
(1+floor(D_H/6))^(r-1).

Let m_H^R(a) be the actual slab multiplicity
at C_H and E_r(H)=sum_a m_H^R(a)^r. For
H<=c log R as above, and fixed r>=1,

    E_r(H) = (R/6) kappa_r(H)
                      (1+O(Q_H/R)).            (3)

Indeed for interior endpoint a in [R,2R-D_H]
all formal ancestors are in the slab, and
in [R-D_H,2R] their actual mass is <=f_H(a).
The excluded boundary has length O(Q_H),
only O(1) periods. In a full period the
weighted sum is M_H kappa_r(H); the difference
between upper and lower totals is
O(M_H kappa_r(H)). Dividing by the main
term yields (3), uniformly without a bound
on the pointwise mass beyond the wall.
The actual endpoint a need not be divisible
by six; sum over all even positions here.
Equation (3) is an exact-period transfer,
not an extrapolation to height comparable
to sqrt R.

## 3. One-level transport and fresh-prime lift

To avoid an off-by-one ambiguity, in THIS
section denote by L_b the first PREheight b
cut, i.e. L_b=C_(b-1). For b>=4 let u(a)
be its mass on a common period for L_b
and L_(b+1), and v the next mass.
The map F_b(a) is determined by starting
at the L_b physical pre-tick state and
running to L_(b+1). If the tick at b is
idle, F_b(a)=a. If it fires, F_b(a)<a on
the physical translated line, because
the gain is positive and no subsequent
position can increase. All intermediate
events have preheight <=b, so the wall
for P_b gives a displacement <6M_b.
The map is well-defined on period residues
and its moving set is exactly the set
where the first tick fires.

Write S(a)=u(a) on fixed points and 0
elsewhere, and I(a)=sum of u(x) over
moving x with F_b(x)=a. Then v=S+I
and the exact energy increment is

    sum v^2 - sum u^2
      =2 sum S I + sum I^2 - sum_(moving x) u(x)^2.           (4)

If at most K moving sources feed any
one destination, and B=sum_moving u^2,
E=sum u^2, then Cauchy gives

    Delta E <=2 sqrt(K E B)+(K-1)B.             (5)

This is a genuine recursion, but K may
be very large; (5) does not assert a
useful upper bound for K.

There is an exact dilution identity for
fresh prime p=2b+1 prime, b>=4.
No earlier tick at preheight <b can use
or test p. The mass u on L_b is periodic
with modulus 6M_(b-1) coprime to p.
Lift to the new period, p times as long.
On positions with even cut tick n=b-a/2
the minus height factor is p itself.
Thus p fires iff a==-1 mod p; no smaller
label can compete at that tick. Parity
is preserved by the old period translation,
and the p coordinate runs through every
residue exactly once. For every r>=1,

    sum_(fresh p firing at L_b) u(a)^r
         = (1/p) sum_(even cut tick) u(a)^r.   (6)

This is an exact finite CRT identity,
and applies even with all previous
merger correlations. The odd cut tick
at that level uses 2b-5, not the fresh
p. Equation (6) estimates the energy
that moves under the newly introduced
prime at its first record level. It
does not bound the energy at its
destination after the whole subsequent
excursion, or at its repeated appearances.
The old-label moving terms and fan-in
remain the essential difficulty.

## 4. Height-capped absorption profiles

Define b_H(a) on P_H-rough canonical
endpoints a (6|a) to be the number of
formal canonical roots whose restricted
P_H trajectory absorbs exactly at a
and whose every completed event has
preheight <=H. Include the zero-gain
root. The cap refers to completed events,
not the indefinitely continued idle
time after absorption. Since P_H
contains 3, all its rough endpoints
are multiples of six. The profile is
periodic modulo 6M_H, and each root
has offset <=D_H. Define

    nu_r(H)=E[b_H(a)^r | P_H-rough],
    V(z)=prod_(5<=q<=z)(1-2/q).

The expectation is the uniform
conditional finite CRT law, including
canonical half-distance parity.
The sum of b_H over a full canonical
period is the number of roots absorbed
before any event of preheight >H.
It is <=M_H (not necessarily equal).
Consequently

    1<=nu_1(H)<=1/V(2H+1)<<log^2(H+2),
    nu_r(H)<=(1+floor(D_H/6))^(r-1) nu_1(H).
                                                               (7)

On a rough endpoint a, C_H is at a
exactly for those height-capped
restricted absorptions: if the cut
is at a, the restricted process had
no eligible event there; conversely
the full process matches all the
height-capped events and no eligible
clock at a can occur before the cut.
Thus b_H is precisely the restriction
of f_H to P_H-rough canonical a. In
particular

    V(2H+1) nu_r(H)<=kappa_r(H).                (8)

Under the endpoint-rough product
law the sequence nu_r(H) is
nondecreasing: lift to the larger
prime period, condition additional
coordinates rough at the endpoint,
and every previously counted
height-capped path remains identical
before arrival (no new prime can
affect any of its ticks). The
endpoint remains restricted-rough.
The smaller profile's conditional
distribution is unchanged by
independent additional roughness.
The probability V(2H+1) nu_1(H)
itself need not be monotone.

## 5. First event above a height cap: synchronization with no small gain cap

For each root let e be its first completed
event with preheight >H, if it occurs by
T. Equivalently this is the next firing
from the source of C_H. The latter may
be after the horizon; in that case no
such completed event is counted.
Suppose its prime p>=64(H+1).
The arrival height at its source a
is <=H. All possible p firing
preheights are >=(p-1)/2. Hence the
wait from arrival is >=p/4.
Since any eligible neighbor prime
has a clock within twice that prime,
the least neighbor prime q(a)>=p/8.
In particular a is P_H-rough and 6|a.
Every possible clock at a has
preheight >=(q(a)-1)/2>H.
Consequently all restricted capped
ancestors of a arrive before the
same stationary first clock from
canonical height 3. Conversely,
any actual path whose first event
above H has such a large p has
exactly a restricted capped
absorption prefix at a, and p is
the stationary winner from h=3.
This proves exact synchronization
without bounding the preceding
gain by O(H) or O(log^2 R).

If the stationary preheight is
b_e, the number of participating
slab roots completing the launch
by T is exactly

    m_e(H,T)= sum_(capped ancestors A of a)
          1{R<=A<=2R} 1{b_e+(A-a)/2-3<=T}.    (9)

For fixed H the full ancestor
profile is b_H(a), not the local
gain profile b_J of 939e39d.
The actual source has at most one
large launch key in this definition.
If b_e+D_H/2<=T+3 and a is interior,
(9) equals b_H(a). The large-clock
phase classification remains exactly
as in 939e39d: postheight 0,p on the
minus side, 3,p+3 on plus.

## 6. Actual weighted high-launch supply and subpower asymptotic

Take H<=c log R, with c small enough
that M_H,Q_H<=R^u for u=1/100.
Let E_r^cap(H;I) sum m_e(H,T)^r over
the large first-event keys of section 5
with p in I. For Y>=64(H+1), Y<=2T+7,

    E_r^cap(H;[Y,2Y))
       <<_r R nu_r(H)/log^3 Y.                (10)

Proof: fix source residue j=a/6 mod M_H
allowed by P_H roughness and fix p
in the band and side. The condition
p|a+/-1 selects a single progression
modulo 6M_H p, since p>2H+1.
Its length X is comparable to
R/(M_H p), polynomially large.
Necessary additional roughness at
free primes 2H+1<q<=min(p/8,R^xi)
gives an upper sieve with two forbidden
classes per q, CRT remainder at most
2^omega(d). Use the standard fixed
dimension-two upper sieve (as in
74a6796 and 939e39d), level sqrt X
and small fixed xi>0. Its product
is O(1/[V(2H+1) log^2 p]), uniformly
also when p is near 64(H+1).
The error is negligible uniformly
relative to X/log^2 R, by the
polynomial length and a sufficiently
small xi. The resulting bound for
the progression is

    << R/(M_H p V(2H+1) log^2 p).

Weight by b_H(a)^r, constant on the
chosen class; sum the allowed classes,
using sum b_H^r=M_H V(2H+1) nu_r(H).
Then sum p by the reciprocal-prime
bound for a dyadic band. The expanded
endpoint interval [R-D_H,2R] still
has length comparable to R.
This proof needs no adaptive transcript
enumeration within the low-height
prefix, regardless of its gain.
Uniform progression bounds allow
multiplication by arbitrary positive
periodic weights, without an error
growing with their maximum.

If in addition Y->infinity,
log Y=o(log R), then

    E_r^cap(H;[Y,infinity))
          ~ (R/6) nu_r(H) V(Y).                 (11)

To prove this, put
Y'=exp(sqrt(log Y log R)).
For Y<=p<=Y', all launches complete
by T for every capped ancestor,
since D_H=O(R^u) and p=R^o(1).
Use the exact stationary winner
certificate (939e39d section 2).
For each allowed residue class and
p pin the free primes have 0,1,2
forbidden residues each according
to the clock comparison. Their
product is uniformly
(1+O(1/log p)) V(p^-)/V(2H+1):
the differences from the full
roughness product are confined to
a constant-ratio band about p.
The dimension-two fundamental lemma
at level sqrt X, with free cutoff
<=4Y'+10, gives relative 1+o(1)
uniformly since log Y'=o(log R);
the progression remainder is
negligible. Weight and sum classes
as before. Use the interior and
expanded endpoint intervals; their
relative lengths are 1+O(D_H/R),
so no pointwise boundary mass bound
is required. Sum both signs and
use 2V(p^-)/p=V(p^-)-V(p).
Finally the upper bound (10) on
the p>Y' tail is O(R nu_r(H)/log^2 Y'),
negligible. This proves (11).

The formal product-coordinate version
is exactly the same stationary
certificate summation, with no
horizon or slab. In particular
the probability the first event
above H has p>=Y is
(1+O(1/log Y)) nu_1(H) V(Y).
This first event exists almost
surely in the full formal process:
all finite even offsets have an
eligible prime almost surely
(product of roughness densities
tends to zero), and every cap is
attained in finite time by (1).

The entire relative history through
this first event has a TV o(1)
actual/formal transfer for
H<=c log R, after shrinking c by
a fixed factor. Indeed for
p<64(H+1) the full prefix and
the next event, if this small,
are determined by a primorial
through O(H): all earlier
preheights <=H and the final wait
<=2p. Uniform residue counting
with the enlarged period <=R^u
gives the claim for any selected
set of small-label histories.
For p>=64(H+1) up to
Y0=exp((loglog R)^2), the capped
prefix histories and offsets
are determined by their root
residue mod M_H. For a specified
p, side and source residue,
choose the subset of its capped
ancestors whose relative
histories qualify; its number is
a nonnegative periodic weight
bounded by b_H(a). Formula (9)
gives the exact physical winner
and the final wait. Apply the
uniform relative exact-certificate
sieve just used, now with cutoff
4Y0+10. Summing the errors for
any selected histories gives o(1)
after normalization, because the
histories partition the root
population for a first event.
All these events fit T (by
D_H+O(Y0)=o(T)). The formal tail
p>Y0 is O(log^2(H+2)/log^2 Y0)
=o(1); hence the unmatched actual
mass, including censored next
events, is o(1) as well. This
is a transfer for the capped
height history, which may have
polynomial gain and duration
bounded by the wall; it is not
a transfer for all histories
through a square-root height.

## 7. Actual stopped gain and the remaining demand

Stop each root at its first
completed event of preheight >H,
or at T if that event has not
occurred. All earlier gain is
<=D_H. The final gain if p<64(H+1)
is O(H+1). For larger labels
sum (10) with r=1 and weights
2Y over the dyadic bands up to
2T+7. The elementary geometric
sum gives

    E_R[G_stop^cap] << D_H+H+1
                         + T nu_1(H)/log^3 T
                      =o(T)                    (12)

for H<=c log R. Indeed D_H=O(R^u)
and nu_1(H)<<log^2(H+2).
This controls long small-height
histories beyond the previous
polylogarithmic gain budget.
It does not bound their later
evolution after the first high
height event. Under hypothetical
finiteness of twins, the earlier
G_T>=(1/3-o(1))T forces

    E_R[G_T-G_stop^cap] >=(1/3-o(1))T.

The bulk gain must be supplied
after leaving this height range.
This remains a necessary demand,
not a contradiction.

## 8. Record-aware pruning of future slow-pair energy

Let (A,B) be a pair with a first
physical merger at a post-tick
state (b,n_m), as in 828a62e.
Let h_m=n_m+b/2. Let M_A,M_B be
their maximum PREheights up to
and including tick n_m, using
birth height 3 as a baseline.
Put M=max(M_A,M_B). Let F be
the maximum preheight at any
common subsequent tick while
both roots are active, i.e.
n_m<n<=earlier retirement.
If there is none take F=-infinity.

The pair shares the first
PREheight L cut, L>=4, precisely
when

    M<L<=F.                                    (13)

The strict lower condition is
important: a firing causing
their first merger has two
different pre-tick positions
or a newly born root. A first
cut at that tick is not shared.
If both previous maxima are
below L, the common future
reaches L before either could
previously have reached it.
Conversely if a first cut is
shared it occurs after merger
and neither prior path has
reached it; then (13) holds.
It follows that (13) is an
exact interval ledger for the
off-diagonal part of the first
height energies, with the
retirement cutoff included.

Fix a top-prime threshold Y
comparable to T. For a pruned
pair in P_I from 828a62e,
let B_e be the preheight of
a common subsequent slow
event of label p>=Y. Call
the pair visible if some such
B_e>M. For d=floor(Y/8)>=1,
call a shared slow event
well-separated if B_e-M>=d.
For a pair with a well-separated
event, choose the first multiple
L of d strictly above M.
Then M<L<=B_e, so it is counted
by the first L cut. For large
Y, L>=4. The number of candidate
grid heights is O(1+T/Y).
Writing C(L)=sum of squared
slab masses at first PREheight L,
N(L)=number attaining it, we have

    P_grid <= (1/2) sum_(L in grid)
                                      [C(L)-N(L)].           (14)

This is valid for arbitrary
length histories. Each pair's
total shared gain is <=2T+6,
so its total contribution
to the gain-weighted off-diagonal
energy at well-separated events
is at most 2(2T+6) P_grid.
If the cut energies at this
finite grid of top heights
were O(R log^2 R), this part
of the large-slow energy
would satisfy the sufficient
top-band bound of 828a62e.
We have not bounded C(L)
at these heights.

There is a further deterministic
cost for the complementary
non-well-separated events.
For each root separately,

    G_at_merge >= 2(M_root-h_m),                (15)

since from the tick attaining
its maximum preheight to the
post-merger state, nonnegative
elapsed time and accumulated
gain obey the height identity;
include the jump on the
maximum-preheight tick.
With baseline 3 the statement
holds also if the maximum
is the birth height.
If B_e-M<d and p>=Y, then
M>(3/8)Y-O(1), since
B_e>=(p-1)/2. If h_m<=Y/8,
(15) implies at least one
root had already consumed
gain >=Y/2-O(1) by the
first merger. If h_m>Y/8
the merger itself occurs at
a high height. These two
classes isolate the recycled
history: one must estimate
earlier large gain before
a low merger, or mergers
at a high height. This
is a cost lower bound,
not an upper count of
either class. In particular
the finite-period cut transfer
(3) cannot be inserted into
(14) at top heights.

## 9. Reproducible audits

All three scripts were executed in the ECMAScript research
runtime, fetched at their exact remote commits and re-executed
with matching output. Reproduce with node. No separate Node
or Lean invocation. The initial larger scratch audit timed out;
the final audit uses the finite ranges below and independent
restricted simulations. No partial scratch result was committed.

A. research/min_local_negative_height_cut_absorption_audit.mjs
   commit fb27fbd1b4a1e355e08218444d651576ee60be75
   blob 795a84054812d8bb2f42d3643b796eefa1a0ff09

Exact canonical periods for H=3,4,5,6,7,8; count
all cut classes and height-capped absorptions,
lift to common periods and verify nesting.
Physical slabs R=3000,12000,48000,192000,
all roots, five caps H=6,12,24,48,96.
Independently restricted simulation with
cutoff 2H+1 checks every first preheight
cut and the capped ancestor root lists
of stationary large launches (including
launches after T, provided their cut is
within T). In R=3000 scan every unordered
root pair and verify the cut interval
identity (13) independently for all
five heights. Counts:

    formal period roots                  191100
    formal period events                 172143
    period nesting checks                191030
    physical roots                        42504
    physical completed events           1033298
    first-height cut controls            212520
    capped absorption controls           120226
    large launch controls                 48694
    exact launch source root-list checks  11873
    physical nesting controls            170016
    independent unordered pair scans     125250
    pair/cut interval comparisons        626250

All assertions passed. Exact finite-period
normalized moments (rounded for display):

    H   M_H     kappa_2(H)     nu_1(H)    capped root fraction
    3      70     1.00000      1.00000       .42857
    4      70     1.00000      1.00000       .42857
    5     770     1.34545      1.24074       .43506
    6   10010     1.65395      1.45589       .43197
    7   10010     1.83277      1.62626       .48252
    8  170170     2.12981      1.77728       .46529

At H=8 max cut gain 66, max cut mass 8,
nu_2=4.24413. For R=192000, N=32001,
T=4958, all five cuts are attained.
The cut energies at H=6,12,24,48,96
are respectively 52929,96543,195427,
357077,598529. The largest maximum
cut gain among those caps is 960.
These are finite observations.
The launch threshold 64(H+1) is
generous; in this largest slab
the timed large-launch root counts
are 442,53,0,0,0. Many beyond-horizon
launches occur at twins. The audit
tests (9) as a source-list identity,
not a numerical verification of
the asymptotic sieve constants.

B. research/min_local_negative_height_cut_fresh_lift_audit.mjs
   commit 88da27ee39947f1659482545f8caf99aafacfe83
   blob 438e71be73b5996fcdf1e896e55a6e3b14f7dc61

Exact one-level pushforward for first
PREheights b=4,5,6,7,8, on common
periods. Count moving sources by
independent direct tick firing,
verify incoming mass and energy
increment, and verify the exact
fresh prime identity (6) for
p=11,13,17.

    period root controls                 191030
    transition comparisons               133712
    pushforward/energy controls          122862
    exact fresh prime identities              3

For b=8 (p=17), normalized even-tick
eligible energy .9558441558, fresh
moving energy .0562261268, exactly
one seventeenth of the former.
Total moving energy .1250572956,
total normalized energy increment
.2970441323. This shows why the
fresh moving term alone is not
the entire increment.

C. research/min_local_negative_pruned_height_visibility_audit.mjs
   commit 07a3e9a0beb6f572b4966d920bea43cbf4ae7d7e
   blob 29114ff16cd7ee9ae316d0951803028ab3661d70

Extend the exact future-slow pair
audit of 828a62e with prefix
preheight maxima and shared slow
event preheights. Same five slabs,
Y=ceil(T/16), d=floor(Y/8).
Check the per-root cost (15),
the grid witness and exact gain
accounting. The pair and event
counts overlap the previous audit,
not independent samples.

    roots                                122505
    events                              3262121
    future slow pruned pairs             1064787
    first merger search steps          40667717
    record interval classifications      1064787
    per-pair prior-drop checks           1064787
    grid witness checks                   832733

    R        pruned     visible    grid     recycled
      3000       799       725       725        74
     12000      6240      5536      5512       704
     48000     41232     35531     34846      5701
    192000    317716    236794    223573     80922
    480000    698800    602134    568077     96666

Here visible/grid count a pair once
if any shared slow event satisfies
the respective condition. At the
largest R the total shared gain
over unordered distinct pruned
pairs is 728644548 (diagonal
excluded, repeated common events
included). Visible-event gain is
596642200, well-separated event
gain 570498662. Of the 96666
nonvisible pairs, 65622 merge
at height <=Y/8 and 31044
at greater height. The finite
percentages are not an asymptotic
bound on the complementary classes.

## 10. Status

The nested PREheight cut supplies
the missing valid partition
recursion, the exact pair interval
ledger and fresh prime dilution.
The height-capped launch profile
extends synchronized source mass
estimates to long low-height
histories and gives actual stopped
mean gain o(T), with no small
polylogarithmic gain assumption.
The main missing estimate is the
growth of C(L) beyond logarithmic
heights and the complementary
recycled-history contributions.
The finite grid bound (14) and
the two cases after (15) specify
these targets. Neither a full
large-slow upper bound nor the
small/intermediate credit upper
bound necessary for the mean
saving below T/3 is obtained.
No twin-infinitude proof or Lean
verification; no changes to
canonical Lean targets, sibling
branches or Context files.
