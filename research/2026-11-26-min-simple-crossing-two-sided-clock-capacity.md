# Two-sided significant-clock stability and mass-deficit capacity

2026-11-26 JST. Continuation of 77f6926cc64f0c9fdfbe57d9bc46960a432a7097.
User requested attacking the already-concentrated stable transport term.
The new unconditional bounds apply to full histories and actual waits,
rather than only q-weighted waits or fixed generations. In particular
they control small-to-medium exact-state masses in narrow phase bands,
at ALL offsets (including small q). No proof of the remaining transport
term, E=O(R^2), twin infinitude, or Lean verification is claimed.

## 1. Use actual wait as the resource

Same common-boundary system: M=R/12+O(1) seeds X in [R,3R/2], 6|X,
initial (X,X/2+3); stop at first U>=2R. Every internal state s=(u,v)
has mass b(s), wait w, chosen label p, and q(u)=min(lpf(u-1),lpf(u+1)).
Deficit d=2v-u. For all non-twin pre-offsets, w<=2q<=2sqrt(2R+1),
and v<=u+1, v>=u/2, n=v+w<=u+3. Twin events at u>=R (R>=6)
double and exit. For a twin-free path the total elapsed wait is
>=R/4-3, whereas the whole physical gain is <3R. If twins are finite,
for all sufficiently large R the total non-twin actual wait W is
>=M(R/4-3)~R^2/48. Thus W=o(R^2) on an unbounded subsequence suffices.
It is enough to control actual wait, not the potentially larger
q-weighted traffic or the offset energy. No equality of these quantities
is assumed.

## 2. Clock-slot capacity with a unique mass-threshold crossing

Include a terminal vertex for each distinct exact exit state, with its
total arriving mass and no successor. Each origin's mass, including
terminal mass, is nondecreasing. For fixed H>=1 an origin can traverse
at most one edge with source mass <=H and destination mass >H. The
total non-twin wait on all such visits is therefore <=2M sqrt(2R+1).
This is a threshold-specific charge, not M log M, and needs no
assumption of stability.

Let I_u be an arbitrary real interval of length ell(u) in which arrival
times v are allowed, for any set of non-twin offsets u. Intersect with
the time envelope if desired; omit offsets with no selected intervals.
Consider all actual origin visits satisfying b(s)<=H and v in I_u.
For the ones not charged as threshold crossings, the successor mass
is <=H. Group those visits at u by their next active tick n (the
least-label tie rule fixes p at n). All source groups in such a slot
merge at the same successor, so their summed mass is <=H. If v0 is
the earliest arrival in that slot, their total wait is <=H(n-v0).
For different slots at fixed u the half-open intervals (v0,n] are
disjoint: if n1<n2, any v in the second slot is >=n1, since otherwise
n1 would be an earlier eligible tick. Each interval is contained
between inf I_u and sup I_u+2q(u). Thus

    W_{b<=H,v in I_u} <= H sum_u (ell(u)+2q(u))
                          + 2 M sqrt(2R+1).                (1)

For unrestricted phases use the envelope and n<=u+3: the sharper
per-offset interval length is u/2+3<=R+3, giving

    W_{b<=H,u in A} <= H(R+3)|A|+2M sqrt(2R+1).            (2)

These are actual all-depth traffic bounds. They allow arbitrarily
many incoming phases and arbitrary earlier mergers. Both include
terminal collisions and do not count an origin twice in the same
offset. They are independent of the previous entropy method.

As a first application, for 7<=T<=sqrt(2R+1), the two-form upper
sieve for u-1,u+1 gives |{non-twin u:q>=T}|<<R/log^2 T:
use the explicit Selberg argument in the inherited record-supply
note, cutoff floor((T/2)^(1/10)), two distinct roots modulo odd
primes, interval length O(R), error O(T^(3/5)) absorbed uniformly.
If T is bounded enlarge the constant. For T=a sqrt R with a>0
fixed, the preceding H_1 rough-supply bound yields the stronger
O_a(R/log^3 R). Hence (2) proves, uniformly over full trajectories,

    W_{b<=H,q>=T} << H R^2/log^2 T + R^(3/2),
    W_{b<=H,q>=a sqrt R} <<_a H R^2/log^3 R + R^(3/2).

In particular H=log R, T=R^epsilon (0<epsilon<1/2), or
H=log^2 R, T=a sqrt R, eliminates those actual waits at
O(R^2/log R). Exact-state b is distinct from offset traffic B;
a large B can consist of many small b at different phases.

## 3. Global mass-deficit tradeoff, including low-q offsets

The sharper new application of (1) uses phase width instead of
roughness of the offset. Put L=ceil(log R) and Hmax=sqrt R L^2.
For any arbitrary reference deficit a(u) (even chosen using the
actual graph), consider all non-twin source states satisfying

    b(s)<=Hmax,    b(s)|d(s)-a(u)|<=R/L^2.

Their total origin-weighted actual wait is O(R^2/log R).

Proof: partition masses into dyadic groups H/2 < b<=H,
H=1,2,4,..., ending at the first H>=Hmax. At level H the
deficit restriction implies |d-a(u)|<=2R/(H L^2). Because
d=2v-u, the permitted v interval has length <=2R/(H L^2).
Apply (1) with mass cap H to this subset (or enlarge to all b<=H
in the same interval). Since the number of even offsets is O(R),
the contribution of this level is

    O(R^2/L^2 + H H_1(R) + M sqrt R),

where H_1=sum_non-twin q(u)<<R^(3/2)/log^3 R is the inherited
three-log supply theorem. There are O(log R) levels and their
caps sum to O(Hmax). Therefore

    W << R^2/log R + Hmax R^(3/2)/log^3 R
                    + R^(3/2)log R
      << R^2/log R.                                       (3)

The statement with a(u)=0 gives the mass-deficit product
b(s)d(s)<=R/log^2 R, up to harmless ceiling constants. The
same proof allows a different arbitrary center at EACH dyadic
mass level and offset. No statistical assumption on phase
distribution and no bound on the number of reachable phases
is used. More generally (1) applies to a union of K intervals
by charging the combined length plus 2K q per offset; charge
threshold-crossing visits once, not once per interval.
This removes actual wait from narrow phase bands even at small q.
It does not bound the full distribution outside such bands.

## 4. Two-sided significant-event stability over polynomial depth

Mark a non-twin event significant if L w>=p-1. The total wait
from all unmarked non-twin events is <=3MR/L=O(R^2/log R),
by total gain <3R per path. A marked event necessarily has
p-1<=2L q. This is an exact clock-dependent filter; it does not
assert a fixed-C efficient graph theorem for the growing L.

For each origin list its marked source states s_1,...,s_k,
m_j=b(s_j). The sequence m_j is nondecreasing, including mass
growth at intervening unmarked events. Fix integer h>=1 and
rho=3/2. Call a marked visit j two-sided stable if both
j-h and j+h exist and m_(j+h)<=rho m_(j-h).
The absent-end visits contribute <=4 M h sqrt(2R+1) wait.
For the rest the rolling log growth log(m_(j+h)/m_(j-h))
is a sum of nonnegative successive log increments, and each
increment appears in at most 2h windows. Thus

    sum_(origins, marked j with both ends) w_j log(m_(j+h)/m_(j-h))
       <= 4 M h sqrt(2R+1) log M.

The actual wait of visits failing the ratio test is bounded
by this divided by log rho. With h=floor(R^(1/4)), the missing
and growth charges together are O(R^(7/4) log R)=o(R^2).
Combined with the unmarked charge this eliminates all except
two-sided stable significant visits, unconditionally. These
have at least h previous and h following SIGNIFICANT events,
not merely large offset displacement; intervening unmarked
events are permitted. The ratio compares the end masses,
not just the mass at the central state.

A two-sided stable origin traverses no light arrival between
those two marked endpoints, since any light arrival doubles
the mass and rho<2. Following the heavy chain backward to
the h-th preceding marked state t(s) and the actual successors
forward to the h-th following marked state r(s) gives the
exact stable mass b(t(s)) if both exist and b(r(s))<=rho b(t(s)),
zero otherwise. The converse follows by forward determinism
for all origins at t(s).

At fixed u, two distinct stable source states cannot have
the same next firing slot: their common next mass b(y) would
satisfy b(s_i)>=b(y)/rho for both i, since both have a future
marked endpoint and total growth <=rho. Their disjoint masses
would sum to >b(y). Consequently stable carrier waiting
intervals (v,n] themselves are disjoint at fixed u. Their
unweighted total length is <=u/2+3, and <=ell+2q when v is
restricted to an interval of width ell. In contrast, arbitrary
unstable source groups at the same offset can share a slot.
This exact structural property provides the clock-specific
version of the phase-capacity bound, though (1) is stronger
for arbitrary histories with a mass threshold.

## 5. Remove large jumps within stable windows

Set J=ceil(R^(7/8)). Each origin has <3R/(J-1) non-twin events
with p>=J by its gain budget. Such an event can belong to the
window from s_(j-h) to just before s_(j+h) for at most 2h
central marked visits (including unmarked intervening jumps).
Each central wait is <=2sqrt(2R+1). Thus the total actual wait
of marked visits whose two-sided window contains any such
jump is O(M h sqrt R * R/J)=O(R^(15/8))=o(R^2) for h above.
This is a genuine all-history charge, not a bound on the
maximal displacement of every stable path. The remaining
window has polynomially many significant events and no
individual jump of size >=J.

## 6. Exact remaining obstacle

Combine the preceding log-merger potential's removal of
recently grown/short spatial ancestry and small B_st offsets
(with w<=2q) with (1)--(3), the significant-event and two-sided
charges, and the large-jump charge. The union of these removed
classes carries o(R^2) actual wait. If twins are finite, the
remaining visits must carry Omega(R^2) actual wait. They occur
at large stable offset traffic; have unique long heavy
ancestry and a long forward continuation with end-to-end mass
ratio <=3/2; have no jump >=R^(7/8) in that marked window;
are significant; and lie outside the mass/phase product
region (3). In particular for b<=sqrt R log^2 R their deficit
must be far from any chosen reference phase at the appropriate
mass level, in the sense b|d-a|>R/log^2 R (up to ceilings).
At q>=R^epsilon they must have b>log R, and at q>=a sqrt R
they must have b>log^2 R. At low q<R^epsilon, a macroscopic
remaining wait would require Omega(R^(2-epsilon)) origin
visits, by w<=2q. This is a dichotomy, not exclusion of either
case. Large exact-state masses and broad phase distributions
are not bounded by the new capacity estimate; a single very
large cohort could still carry substantial wait. The previous
abstract stable-chain obstruction persists, and no proof of
the residual estimate or of E=O(R^2) has been obtained.

## 7. Executed audit

Source research/min_simple_two_sided_audit.py at
167b357e198914a5355febcb8adeaa5173b59c80, blob
8f785820b14479d699367ff6a5d45f2d92fa7a36, exact remote readback
matches locally executed source. Stdlib + inherited audit.
Run:

    python research/min_simple_two_sided_audit.py 1000 10000 100000 1000000

All four graphs reproduced earlier state/origin totals. Verified
unique mass-cap crossing (including exact terminal masses),
disjoint clock slots and time-band capacity, dyadic mass/deficit
product bounds for a=0 and the graph-dependent midpoint of
min/max deficit at each offset, rolling marked growth budget,
two-sided stable mass by independent origin replay versus
heavy-ancestor reconstruction, and big-jump window counts.
The logarithmic comparisons use floating arithmetic with
tolerance; mass, phase, and ratio checks use integers.
At R=1000000, M=83334, states=294268, L=14, total non-twin
actual wait=66822800, unmarked wait=269145.

    h   stable states  stable actual wait  missing ends    growth-excluded
    1   156342         44022888            4283212         18247555
    4    60236         29490724           15506032         21556899
    16    9623          9130632           43293924         14129099
    31    2161          1964875           57736799          6851981

The h=31 sample has high-q (q>=250) stable wait 923065;
519837 of it has b<=191 (ceil(log^2 R)); max high-q source
mass 366. All-history small-group high-q wait (q>=250,b<=191)
32830069, of which threshold-crossing wait 1314050, from
2361 origins. For q>=31,b<=14, corresponding all-history wait
16098928, crossing wait 7159425, from 30351 origins.
Using Hmax=(floor(sqrt R)+1)L^2=196196 and product limit
R/L^2=5102.04: zero-centered region has 257589 states and
36658959 actual waits (16779290 threshold-crossing); midpoint
center has 254475 states and 31763659 waits (13650416 crossing).
These populations overlap with other excluded classes, so
their finite wait counts must not be added. No non-twin jump
>=ceil(R^(7/8)) occurred in the four tested graphs, so the
positive big-jump case of the charging lemma is not exercised.
All origins reach twins in these finite slabs as before.
The bounds in this note are mathematical deductions, not
asymptotic extrapolations from the samples; no Lean kernel run.

Next focus: bound the joint large-mass/large-phase-width
stable transport using arithmetic of actual successive clocks,
rather than simply introducing more unproved traffic conditions.
