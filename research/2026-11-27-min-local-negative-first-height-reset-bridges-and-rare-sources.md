# Negative MIN: first-height reset bridges, terminal excursions, and rare reset sources

2026-11-27 JST. Continuation of d9f604961c86ff53270847646e3055f6b8932c35.
Derive a finite canonical/phase-6 restart after every top-band reset
before first height H, a terminal-excursion witness criterion, and
unconditional upper bounds for distinct inexpensive reset sources and
same-class collisions near the square-root scale. The required
unbounded small-gain first-passage sequence is not established.

## 1. First-height passage and exact top reset threshold

Write x=a/2, h=x+n at actual absolute time n. At the
next tick put b=h+1. Only odd primes dividing 2b+1
(even clock, minus direction) or 2b-5 (odd clock,
plus direction) can fire. The actual winner is the
least eligible prime in this factor list, as in
0116e3e. The idle update is h->b and a firing p
updates x->x-(p-1)/2, h->b-(p-1)/2. The height
is nonnegative and increases by at most one per tick.

Start a seed with height h0 in {3,6} below integer
H>20. Let tau_H be the first time the height AFTER
processing the tick reaches H (relative to seed).
One must not count an event's PRE-firing height H
as a first passage. Every completed event before
passage has b<=H, p<=2H+1. If

    p>(2H+1)/3,

then in the minus case (2b+1)/p is a positive odd
integer strictly below 3, hence equals 1. In the
plus case the same holds for (2b-5)/p: for these
large p the small negative possibilities cannot
be divisible by p. Therefore the post-firing h
equals 0 (minus) or 3 (plus), exactly.
In both cases the new x is even, since n has
the appropriate parity (even at h=0, odd at h=3).
This sharpens the simpler p>H reset observation.
Hereafter call these labels top resets. All other
events in an excursion have p<=(2H+1)/3.

The physical process is used only while positive
distances and negative times remain in the relevant
slab; in the finite controls below stop at gain
budget 2H. A first passage in the formal congruence
extension exists by the finite-alphabet wall bound:
all labels before H are <=2H+1, hence total possible
gain while remaining below H is bounded by the
periodic wall distance, and idle time eventually
forces passage. This gives no useful near-square-root
bound on the gain or assurance that an arbitrary
physical root stays in its slab until passage.

## 2. Exact bounded bridges to phase 3 or 6

A reset to h=0 with x even always reaches
x divisible by 3, h=3, within 8 ticks and with
full gain <=10. All firing labels in this bridge
are 3 or 5. Proof by the following explicit cases:

* At h=0, even x, the first tick is odd with
  height expression -3. If x=2 mod3, the p=3
  event occurs, and the next even tick also fires
  3. The two jumps keep h=0 and reduce x by 2;
  x is again even, now 0 mod3. Otherwise the
  first tick is idle, at h=1.
* From an even x not 2 mod3 at h=0, the next
  two ticks reach h=2 unless the second tick,
  whose expression is 5, fires p=5 (exactly
  x=2 mod5). That firing reduces x by 2, keeps
  h=0 and gives x=0 mod5.
* After this possible p=5, the two p=3 events
  may again occur if x=2 mod3; in that case x
  decreases by 2, hence becomes 3 mod5, so no
  second p=5 can fire at height 2. Across the
  whole bridge the pair of p=3 events occurs
  at most once: if it occurred before p=5,
  the subsequent p=5 changes x mod3 from 0
  to 1, not 2.
* At h=2, the next odd tick has expression 1,
  so reaches h=3 with x even and x=0 or 1 mod3.
  If x=1 mod3 the next even tick (expression
  9) fires p=3, leaving h=3 and x=0 mod3.

Thus there are at most two initial p=3 events,
one p=5, and one final p=3. Full gain <=10;
time =3+gain/2 <=8.

For reset h=3, even x:
* x=0 mod3 is already a standard seed.
* x=1 mod3: one p=3 at next tick gives a
  standard seed.
* x=2 mod3: first tick idle (expression 9,
  p=3 ineligible). At the next tick the
  expression is 5; if p=5 fires, height is
  3 and x decreases by 2 to 0 mod3.
  Otherwise reach h=5. The next even tick
  has expression 13. If p=13 fires, height
  becomes 0, x decreases by 6 and remains
  even. Apply the preceding 8-tick bridge.
  If 13 does not fire, reach h=6. The next
  odd tick has expression 9, p=3 fires
  (x=2 mod3). The following even tick has
  expression 15 and the least p=3 fires.
  Both jumps keep h=6 and together reduce
  x by 2 to 0 mod3.

Consequently the reset h=3 always reaches
a seed with x=0 mod3 and height in {3,6},
within 11 ticks, full gain <=22. All heights
during either bridge are <=6 and the only
possible firing labels are 3,5,13. The phase-6
seed resulting from the last case has even x.
It is NOT asserted that this phase is always
reachable from the same distance's standard
height-3 birth. The extended seed family
(a divisible by six, h0=3 or 6) is used
explicitly. Since all tested congruences depend
only on x mod 390, the 195 even residue classes
for each starting height are a complete finite
certificate. The direct arithmetic above
establishes that no omitted prime can fire.
The bounds are attained in the finite residue
table, not merely loose maximum estimates.

## 3. Terminal-excursion criterion

From any such seed of distance B, define G to
first passage H, W the elapsed waits of completed
events and I the final idle duration. The height
identity and mod-30 potential give

    tau_H=H-h0+G/2,
    I=tau_H-W >= H-h0-7G/4-8
               >= H-7G/4-14.                   (1)

Every non-twin endpoint in [R-O(H),2R] has
I<next wait<=2S, S=sqrt(2R+1). At H=ceil(4S)
this implies

    G > (4/7)(H-2S-14) = (2/7)H-O(1).          (2)

Thus G<=H/4 certifies a twin endpoint for large
R. More generally liminf G/H<2/7 suffices along
unbounded local seeds of either phase. If such
a seed starts at a genuine reset bridge, the
claim concerns its suffix, not the original
path's accumulated gain. Conversely infinitely
many twins supply standard seeds with G=0 at
this height, so the existential extended-seed
criterion is equivalent to twin infinitude.
It is not necessary to prove a small-gain
statement for all original standard roots.

A physical original root can be split after
each top reset and its bounded bridge. If it
reaches H before leaving the slab, let G_tail
be the gain from the last restart seed (or
the original seed if no reset). There are no
top resets in this terminal excursion, and
(1)-(2) apply to its gain alone. Even if the
total gain from the original root greatly
exceeds H/4, its terminal excursion may be
a valid witness. The bridge does not itself
hit H because H>20. For first passage with
total gain <=2H from [R,2R], both the restart
and endpoint remain at distance >=R-2H;
negative time and physical half-distance
constraints are automatic for large R.
For longer original prefixes, explicitly
require the endpoint to remain of scale R.

For H=4 floor(sqrt R/(log R)^B) with fixed
B>0, (1) also shows G_tail<=H/4 implies
I>2K for K=H/4 and sufficiently large R.
Then the endpoint is K-rough. Apply the
distinct endpoint/selected energy criterion
from d9f6049 to this suffix-success population,
with care to count distinct roots or seeds
and not multiple occurrences of the same seed.

## 4. Expensive versus slow top reset

Consider a completed top reset p in an excursion
starting from phase h0<=6. Let G_pre be gain
from that seed up to the arrival at the source a
of this reset, excluding the reset jump. Let w
be its own wait. The arrival height satisfies

    h_arr=h0+W_pre-G_pre/2
          <=14+7G_pre/4,

by the universal mod-30 potential. The top
reset preheight b is (p-1)/2 (minus) or
(p+5)/2 (plus). Hence

    w=b-h_arr >= (p-1)/2-14-7G_pre/4.           (3)

If G_pre<=p/7, then w>=p/4-14.5>=p/8
for sufficiently large p. Every odd prime
q<p/16 dividing either neighbor of a would
have fired earlier than this event (wait<=2q).
Therefore each such inexpensive top reset
has a source with both neighbors p/16-rough,
and a selected prime p in the top band.
Call a top reset slow if its actual wait is
>=p/8. Inequality (3) shows inexpensive resets
are slow asymptotically. A non-slow reset
must have spent a positive multiple of H
in gain BEFORE its own jump. This is a
necessary dichotomy, not an upper bound
on excursion cost.

## 5. Unconditional count of distinct slow-reset sources

Suppose H is either a fixed positive constant
times sqrt R, or comparable to sqrt R/(log R)^B
for fixed B>0. Restrict actual sources to
[R-O(H),2R]. All top reset primes are in a
constant-ratio interval [cH,CH], c>0; their
logarithms are comparable to log R.

Fix p and direction. A possible slow source has
one neighbor pm, and the other pm+/-2, with
m in an interval of length O(R/p). The roughness
condition above implies both m and pm+/-2
avoid odd prime factors below p/16 (if m=1
it would imply a of order H, outside the slab).
Use the two-dimensional upper sieve already
applied in d9f6049 at cutoff (R/p)^epsilon
for sufficiently small fixed epsilon. This is
below p/16, and p itself is outside the sifting
range. The two prohibited residues are distinct
for each odd sifting prime. The usual squarefree
CRT remainder <=2^omega(d) and level sqrt(R/p)
give the uniform bound O(R/(p log^2 R)).
Summing over the constant-ratio prime band
uses sum_p 1/p=O(1/log R), so

    # distinct slow top-reset sources
    (including label and direction)
                  << R/(log R)^3.              (4)

At a fixed a,p,direction the top reset height
b is uniquely determined, hence so is the
absolute firing time n=b-a/2. This bounds
physical reset keys, not merely spatial
positions, and needs no cohort equidistribution.

It follows, for example, that canonical roots
whose FIRST top reset is reached with G_pre<=L
and G_pre<=p/7 number at most
O((L+1)R/log^3 R): the root lies in [a,a+L]
and is divisible by six. Thus for
L=o(log^3 R) such first inexpensive resets
occur for only o(R) roots, unconditionally.
The bound is on the selected event, not on
the entire low-gain population or first passage.

More generally choose a subset of initial roots
and mark at most one slow reset per root
(e.g. its first one). Let E_s be sum of squared
multiplicities at the marked physical keys.
By Cauchy-Schwarz the number of marked roots
is O(sqrt(R E_s/log^3 R)). In particular if
E_s/R=o(log^3 R), only o(R) roots are marked.
For selected initial populations of size
Omega(R), the energy scale O(R log^2 R)
would suffice to suppress such cheap resets.
This energy bound is not established here.

## 6. Same-type restart collisions

A top reset of label p sends source a to
raw arrival b0=a-p+1. For a minus reset,
p divides b0; for plus, p divides b0-2.
The finite bridge then sends it to B=b0-d
with even d in [0,22], phase 3 or 6.
For fixed B, direction and bridge gain d,
possible p in the top band must divide
B+d or B+d-2, as appropriate. Since
p>=cH=R^(1/2-o(1)), these positive
integers of size O(R) have at most two
distinct such factors for sufficiently large
R. Each p fixes source, preheight and
absolute time uniquely. The total number
of distinct reset keys leading to a given
restart seed is therefore bounded by an
absolute constant (at most 2*12*2=48,
even without fixing the phase). No bound
on the number of original roots entering
each key follows from this.

There is a sharper asymptotic for collisions
WITHIN the same direction and bridge gain
(and, if desired, same resulting phase).
Suppose two distinct slow top resets with
labels p,r have the same restart B and
same direction and d. Their raw arrival b0
is the same. Necessarily b0-c0=pr k, where
c0=0 for minus and 2 for plus, and k is
a positive integer <=O(R/H^2). In fact k
is even. The p-source neighbors are

    p(kr+1), p(kr+1) +/- 2,

with the sign determined by direction.
Therefore r, kr+1, p(kr+1)+/-2 all avoid
odd primes <=a sufficiently small fixed
power of H, using slow source roughness
and primality of r. Fix k,p. Sift r in
[cH,CH] with these three linear forms.
Outside primes dividing 2 k p (p+/-2)
the three roots are distinct. This product
is nonzero and polynomial in R, uniformly
in k,p. Excluding its prime factors costs
at most O((loglog R)^3) in the usual
dimension-three sieve product: split bad
primes at log R, use Mertens for the
smaller ones, and the polynomial product
bound for the sum of reciprocals of larger
ones. Exclude the finitely many primes
<=3 as well. Apply the standard upper sieve
at cutoff H^epsilon, level sqrt H; CRT
remainder <=3^omega(d), summed error
O(sqrt H log^2 H). This gives

    O(H (loglog R)^3/(log R)^3)

values of r uniformly in fixed p,k. There
are O(H/log R) primes p and O(R/H^2)
possible k (if that upper range is <1
there are no pairs). Summing and allowing
the finitely many bridge gains/directions
gives the unconditional upper bound

    # same-class slow reset collision pairs
        << R (loglog R)^3/(log R)^4
         = o(R/(log R)^3).                     (5)

This proof does NOT estimate collisions
between the different directions or bridge
gains; those are handled only by the
constant multiplicity bound. Nor does it
prove that the actual slow reset set has
size comparable to R/log^3 R. If it does,
the within-class collision loss is lower
order at that scale. In particular the
many-parent mass at an actual reset key
must be distinguished from many different
keys mapping to the same restart. These
bounds are for the latter, not the former.

The sieve input in sections 5-6 is the
same standard fixed-dimension upper
sieve as in prior notes (see 74a6796,
2021e5a and d9f6049 for the fundamental
lemma reference and CRT remainder
argument). No lower sieve or new
independence assumption at sqrt R used.

## 7. Optional cutoff coupling and its limitation

For an exact restricted rule allowing p<=P,
with P=floor((2H+1)/3) and including 3,5,
the same mod-30 potential holds, since its
proof relaxes larger labels and retains
3,5 priority. Consider a set of canonical
seeds whose restricted first-H passage has
gain <=L, with L<=P/8. Physical boundaries
are irrelevant if H=o(R) and slab size R.
Before the first divergence the unrestricted
process follows the restricted one. Any
divergence is an omitted top reset p>P,
with pre-gain <=L, so it is slow by (3).

All diverging roots at a common source a
are at that same a at common height
J=floor(P/2)-2 BEFORE divergence, for
large H: the arrival height <=11+7L/4<J
and divergence preheight >=(p-1)/2>J.
Thus they already coincide in absolute time
at J-a/2 and have the same restricted
first-H endpoint. Restricted trajectories
are well defined there, and have not yet
hit H. The squared masses at distinct
divergence sources sum to at most the
restricted successful endpoint energy C_res.
By (4) and Cauchy-Schwarz, at most

    O(sqrt(R C_res/log^3 R))

restricted successes are lost by preemption.
In particular a positive-density restricted
success cohort with C_res=o(R log^3 R)
would retain a positive fraction of genuine
successes. This is conditional. For H=4S,
the cutoff P already exceeds S, so a
restricted low-gain first-H endpoint itself
certifies a twin; for near-sqrt H its
roughness can likewise be used directly.
The coupling is of interest for actual
trajectory comparison, not a purported way
to evade the lower-sieve problem. No
unconditional restricted low-gain mass
estimate near sqrt R is derived.

## 8. Executed finite audit

Source research/min_local_negative_reset_bridge_first_passage_audit.mjs
commit 42c5f3415d5cfdf7407934699e5c34d32d1c6159,
blob 54d543b57132133c064ed71fdb9a61b7795be797.
Executed in ECMAScript research runtime, fetched at exact
commit and re-executed with identical output. Reproduce
with node on this source; no separate Node or Lean run.

Complete bridge enumeration: x=780,782,...,1168,
each h0=0 and 3, covers all 390 even-x/height
classes mod390. 1263 tick evaluations; all 390
bridges independently checked by direct factorization
of a+/-1 and next-event computation. Max time 11,
max gain 22; h0=0 max time 8/gain10.
There are phase-6 cases, so assuming all plus
resets return to phase 3 would be false.

Actual standard seeds in four slabs R=48000,192000,
480000,1000000. For each slab run H=ceil(4S) and
H=4 floor(sqrt R/sqrt(log R)). Event-jump first
passage, stop if gain would exceed 2H (bridge may
complete just beyond cap, then stop). All actual
sources stay positive and negative-clock time is
within the slab. 573340 root/horizon controls,
14960555 main-loop completed event evaluations
(excludes bridge events), 534389 attained passages,
38951 gain-budget stops. 42226 top-reset incidence
checks, 42226 physical bridge comparisons, 534389
suffix inequalities. 17938 inexpensive reset
incidences; all are slow (w>=p/8) in these
controls. 3355 distinct restart multiplicity
checks; zero same-class slow collision pairs
observed. Therefore the numerical collision
factor check was vacuous, and (5) is an
analytic derivation, not independently verified
by observed collision examples. No direct
restricted-coupling simulation in this audit.

At the larger square-root height:

    R        roots   reached H   gain<=H/4   tail<=H/4   extra
    48000     8001      7935         4747        4788       41
    192000   32001     31784        19825       19830        5
    480000   80001     79998        53285       53341       56
    1000000 166667    166377       115938      116165      227

All 194124 suffix witnesses at larger H
have actual twin endpoints. 329 incidence
witnesses newly included by using terminal
gain instead of total gain. These are finite
examples, not evidence for an unconditional
asymptotic saving in the finite-twins regime.

At the smaller H=4K:

    R        top reset incidences  distinct keys  distinct inexpensive slow keys
    48000              1176              150           132
    192000             5444              483           433
    480000            11765              965           891
    1000000           23361             1748          1615

The mean total vs terminal gain divided by H,
CONDITIONED on reaching H within budget 2H,
at R=1000000, H=1076, is .55686 vs .45235.
For H=5657 it is .21249 vs .21013. Budget
stops are excluded from these means; they
must not be reported as unconditional
ensemble mean estimates. Slow-source
asymptotics (4)-(5) are upper bounds,
not fitted laws from these finite samples.

## 9. Remaining target

The previous G_H<=H/4 target may now be
replaced by a terminal excursion from a
phase-3/6 restart with no top labels and
gain <=H/4, while remaining in an unbounded
physical slab. Cheap top reset keys are
unconditionally sparse at order R/log^3 R,
and same-class regeneration collisions have
a further log saving. These are useful
upper bounds on one component, but neither
implies that the terminal excursions have
small gain. The main missing result remains
an unbounded low-gain first-height sequence
or sufficient near-square-root rough endpoint
excess. In particular no asymptotic upper
bound below (2) on the full or terminal
gain was obtained. No twin-infinitude proof,
no Lean verification, no canonical Lean
target or sibling branch changes.
