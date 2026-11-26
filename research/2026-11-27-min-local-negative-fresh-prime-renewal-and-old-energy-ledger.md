# Negative MIN: exact fresh-prime renewal, weighted excursion bounds and old-energy ledger

2026-11-27 JST. Continuation of ddd94741bd33ea674ea8952ba563037fe6fc32d8.
We extend the fresh-prime dilution at a single record preheight to its
ENTIRE effect through the next record, including repeated fresh
firings and merger with stationary or moving old cohorts. This
yields an exact 1/p-normalized energy increment on the old period.
The bounded height-zero bridge gives a canonical-profile fan-in bound
for reset excursions. Short reset excursions are injective on the
activated lift, and the remaining incoming energy has a weighted
displacement bound without a maximum-fan-in assumption. An all-height
finite-slab ledger isolates the contribution of old labels, which
accounts for most observed energy growth. The proposed logarithmic
energy estimate, its square-root-scale transfer, and the twin-prime
contradiction are not established. No Lean verification or literature
priority claim.

## 1. Conventions and old-only next cut

Use first PREheight L_b, b>=4, as in ddd9474 (L_b=C_(b-1)
there). At the cut, position a is the pre-tick source,
n=b-a/2. The next tick at a has the height-local factor
2b+1 if n even, 2b-5 if n odd. A firing p reduces a
by p-1 and postheight by (p-1)/2. All heights before
L_(b+1) are <=b at completed firings.

Let p=2b+1 be prime, p>=11. Write P^- for odd primes
<p, Q their product, L=4Q, M=L/6=2Q/3. This is an
old canonical spatial period, preserving the clock
parity under a translation by L. Let U(a) be the
mass at first preheight b+1 when using P^- only
from canonical seeds h=3, with no horizon censoring.
It is periodic modulo L. There are M canonical
root classes, and sum_(even a mod L) U(a)=M.
Use K_r=(1/M)sum U(a)^r for its normalized moments.
These old-exit moments differ from the actual
first-b moments kappa_r(b-1) in ddd9474: old-label
transport from b to b+1 has already occurred.

Before first b+1, p can fire only at PREheight b
with n even and a=-1 mod p. The odd factor at b
is p-6; earlier factors cannot involve p. At
every such even b tick the OLD rule necessarily
idles, because 2b+1=p has no old prime factor.
Thus an old trajectory has at most ONE such
even-b opportunity before exiting to b+1. It is
its last tick before the old first b+1 cut.
This is the key to avoiding repeated tests along
the whole preceding old history.

Consequently the partition of canonical roots at
their old first b+1 is preserved as a refinement
of the NEW first b+1 partition. An old exit at a
moves under insertion of p iff

    b-a/2 even, a == -1 mod p.                 (1)

If not, all its prior path and its exit are unchanged.
If yes, the entire old exit cohort is redirected
at the same physical even-b tick. This assertion
does not assume independence of any old histories.
It also holds for a fixed finite set of physical
roots whose relevant exits exist, regardless of
whether their old exit mass is periodic.

## 2. Complete insertion renewal on the old period

Lift the old period L to Lp. For each even position
class x mod L with b-x/2 even, there is exactly
one activated lift A_x mod Lp satisfying (1).
Denote this index set by X. The mass at that lift
before insertion is U(x). In particular for any
r>=1 the activated mass moment, divided by pM, is

    (1/(pM)) sum_(x in X) U(x)^r
      = (1/p) K_r^even.                         (2)

Here K_r^even is the old-exit moment restricted
to the even-b clock class, normalized by M.
This is a lift of the OLD EXIT profile, not just
the initial mass at first b. It accounts also for
old-label motion before the fresh activation.

From A_x the p firing resets to h=0 at

    A'_x=A_x-p+1, A'_x == 0 mod 4p.

Run the OLD process from this reset to its first
preheight b+1. Write d(x) for its gain and

    c=A'_x-d(x).

The gain d(x) and c mod L depend only on x, not on
the choice of lift by Lp. If c satisfies (1), the
old process would idle at b again and the new p
must instead fire there. Repeat the procedure.
If c does not satisfy (1), exit at c. This defines
a renewal graph on the activated residue classes.
Its edges between activated nodes are computed
with old-alphabet reset excursions only. A repeated
p requires

    d(x) == 1 mod p, d(x) even,
    d(x) >= p+1.                                (3)

Indeed c=A_x-(p-1)-d(x), so c=-1 mod p iff
d(x)=1 mod p. The parity of the next even b tick
is also required; (3) is only necessary.

The graph has no directed cycle. The P^- union
{p} process at preheight <=b cannot cross a
spatial wall of half-distance a/2 divisible by
Qp. Its total displacement is <=2(Qp-1)<Lp.
Any cycle modulo Lp would produce a positive
multiple of Lp in displacement. Every branch
therefore terminates. Let y_x mod Lp be its final
exit, D_x>=p-1 its TOTAL gain since activation
(including p and all old excursions).
The wall bounds D_x< Lp, so it determines a
unique displacement to the terminal lift.
All final exits are nonactivated. The graph can
be computed by memoized terminal resolution,
with no enumeration of all p lifted old roots.

## 3. Exact energy increment including repeated fresh firings

For a nonactivated exit y mod Lp set

    I(y)=sum_(x in X: y_x=y) U(x).

The new exit profile equals the old lifted
profile, minus its U(x) at every activated lift,
plus I(y) at the nonactivated exits. This is an
exact pushforward on the full periodic extension.
Let K_2^new be its normalized moment (per pM).
Then

    K_2^new - K_2
      = (1/(pM)) [
           2 sum_y U(y mod L) I(y)
         + sum_y I(y)^2 - sum_(x in X) U(x)^2
        ].                                      (4)

All terms on the right, except the explicitly
displayed factor 1/p, are computations over
old residue classes or their terminal images.
In particular the p coordinate does not need
to be sampled anew for each repeat. It is
fixed by the initial activation; subsequent
positions are determined. Neither replacing
multiple firings by independent Bernoulli
tests nor assuming that their images are
distinct is justified.

The bracket is nonnegative: the last two terms
differ by the cross-products of distinct
activated cohorts sharing a terminal exit.
One can equivalently write (4) as

    Delta_fresh K_2 = (2 A_p+B_p)/p,
    A_p=(1/M)sum_x U(x) U(y_x mod L),
    B_p=(1/M)(sum_y I(y)^2-sum_x U(x)^2)>=0.

The first is the old stationary-exit cross term,
the second is collision energy between activated
cohorts. Both depend on old-profile correlations.
The exact 1/p factor alone is not a bound on
their size as p increases.

## 4. Canonical bridge and reset fan-in

For an activated x, the reset A'_x has h=0
and even half-distance. The bounded bridge in
5b148fe (first-height-reset-bridges) reaches a
canonical seed B, h=3 and 6|B, within 8 ticks
and gain <=10. It uses only 3 and 5, with
preheight <=4, so lies strictly below b>=5.
This bridge is available in the old rule.
Hence the OLD reset excursion ending at c
factors through the canonical old exit of B.

On the OLD period, the possible reset seeds
A'_x are exactly the classes divisible by 4.
For any fixed canonical B there are at most
three such seeds in [B,B+10], including
periodic translates. Thus for the first
old reset exit map rho(x)=c mod L,

    # {x in X: rho(x)=y} <= 3 U(y).            (5)

This is an unweighted number of reset source
classes, not their inherited U(x) mass.
No bound on the old reset gain is needed.

The set of final nonactivated exits of the
full renewal graph is a subset of the image
of LAST old reset excursions from activated
nodes. For each old residue y, the number of
different terminal lifted keys with that
old residue is therefore also <=3 U(y).
Consequently

    sum_(terminal lifted y) U(y mod L)^2
                         <=3 M K_3.           (6)

The sum in (6) is over distinct terminal keys,
not paths, and counts only one key when many
chains have the same last activated node.
This retains the dilution in the cross term
even with repeated fresh firings.

## 5. Short versus long reset excursions

Call an activated source short if its first
old reset excursion has d(x)<=p, long otherwise.
A short one cannot repeat by (3), and its
whole displacement from activation to exit
is <=2p-1. All activated physical sources
lie in a single class modulo 4p by (1).
Thus their spacing is 4p, and different short
sources cannot have the same final position.
The conclusion also holds on the Lp-periodic
lift, by translating representatives to the
same final position. Let I_s,I_l denote the
incoming masses from short and long sources.

The short internal energy cancels exactly:

    sum_y I_s(y)^2 = sum_(short x) U(x)^2.

By (5) and Cauchy, the contribution from the
old base mass crossed with short arrivals
is bounded by

    (2/(pM)) sum_y U(y mod L) I_s(y)
                       <= (2/p) sqrt(3 K_2 K_3).             (7)

The third moment occurs because the number of
old reset classes mapping to y can be as large
as a constant times U(y). There is no assumption
that the old masses are spatially independent.
This bound does not by itself close a recurrence
for K_2 alone.

The long source classes have a canonical old
gain tail description. Let eta_p be the fraction
of old canonical roots whose gain at first b+1
is >p-10. If d(x)>p, after its bridge of gain
<=10 the canonical seed has old cut gain >p-10.
The same factor-through argument gives

    # {long x} <= 3 M eta_p.

Therefore for r>=1,

    (1/(pM)) sum_(long x) U(x)^r
                         <= sqrt(3 eta_p K_(2r))/p.          (8)

This estimates the initial long moving mass
or energy, not its energy after renewed merging.
For that we need to control total displacement.

## 6. Weighted displacement estimate for long incoming energy

Choose any positive weight w(t) on t>=0 which is
nondecreasing and for which

    C_w=sum_(j>=0) 1/w(j) < infinity.

For example w(t)=(1+t)^(1+epsilon), epsilon>0,
or a constant multiple of
(1+t) [log(2+t)]^(1+epsilon).
The latter requires a smaller displacement
moment than a quadratic weight.

For each terminal lifted position y, take physical
representatives of its long activated ancestors,
with the exact total gains D_x (not displacements
rounded modulo the old period). They differ by
multiples of 4p, and lie on or above y. Thus the
numbers D_x/(4p) in this group have spacing at
least one and are nonnegative. Weighted Cauchy
gives

    I_l(y)^2 <= C_w sum_(long x:y_x=y)
                      U(x)^2 w(D_x/(4p)).

Define the old-period normalized weighted moment

    Lambda_p=(1/M)sum_(long x) U(x)^2 w(D_x/(4p)).

Then

    (1/M)sum_y I_l(y)^2 <= C_w Lambda_p.       (9)

This is valid without a uniform bound on the
fan-in or the number of renewal steps. The
total gain includes the whole renewal chain;
substituting just its first old excursion gain
would not justify (9).

In (4) use I=I_s+I_l, cancel the short internal
energy, and drop the negative long removed
energy. Apply (6) to the base-long cross term,
Cauchy to the short-long cross term, and (7),(9).
The result is

    Delta_fresh K_2 <= (1/p) [
        2 sqrt(3 K_2 K_3)
        + 2 sqrt(3 K_3 C_w Lambda_p)
        + 2 sqrt(K_2 C_w Lambda_p)
        + C_w Lambda_p
    ].                                         (10)

This strengthens the earlier single-tick
dilution into an inequality for the entire
fresh-prime excursion including repeats,
with explicit old higher moments and an
old-period weighted excursion tail.
There is no p^(-1/2) loss in (10).
The formula is useful for distinguishing
long paths from short ones, but the terms
K_3 and Lambda_p have not been bounded
at the needed orders.

For a possible sharper closure, the exact
correlation A_p in (4) can be estimated
directly instead of the K_3 bound (7).
For example A_p+B_p=O(K_2) would give
a multiplicative 1+O(1/p) fresh increment;
iteration over primes alone gives at most
a power of log p, not necessarily exponent
two. Old-label transport must also be
controlled. This is a conditional target,
not an assertion about those correlations.

## 7. The old-label energy ledger on every height

For a fixed root set attaining all cuts under
consideration let E(b)=sum_a m_b(a)^2 denote
the physical first-preheight b energy.
Censoring is handled by choosing the SAME
survivor set at every level; for the finite
tests below all slab roots survive through
the maximum cut. When p=2b+1 is prime,
let E^-(b+1) be the old-only cut energy
with p omitted. Then

    E(b+1)-E(b)
       = [E^-(b+1)-E(b)]
         +[E(b+1)-E^-(b+1)].                   (11)

Both differences are nonnegative by the
nested first-height partition and the
old-exit refinement of section 1.
If 2b+1 is composite, there is no new
prime at this level and put the entire
increment in the old term. The first
possible plus height of an odd prime
is later than its first minus height,
so there is no separate fresh prime
introduced by the odd clock at b.
This convention counts every increase
exactly once. It includes repeated old
and fresh labels and arbitrary histories.

For actual roots, E^-(b+1) can be
computed without independent replay of
all old processes. On the full path up
to first b+1, record its FIRST p firing
at preheight b before that cut, if any.
The old cut is its source at this first
fresh firing; if none, the old cut
equals the full cut. The old process
matches the prefix up to that event
and idles at b, so this is exact.
Thus collect per-position intervals
of record heights for the full path
and sparse signed mass corrections at
fresh levels. A height sweep computes
all E(b) and E^-(b+1) in one pass.

The numerical outcome is significant:
fresh insertions account for only
about 21-27 percent of total cut
energy increase in the tested slabs.
The old-label terms in (11) account
for the majority. Thus even a proof
of a sharp fresh-prime increment
would leave the old recurrence open.
Also, the observed normalized cut
energy divided by log^2(height) grows
across these finite heights. This
does not disprove an O(log^2 H)
bound, which permits an absolute
constant and asymptotic crossover,
but gives no numerical basis for
assuming saturation of that bound.

The proposed square-root height
energy bound C(H)<<R log^2 H
from ddd9474 remains open.
The new (4),(10) are exact
finite-period statements. They
do not transfer the uniform
1/p dilution to actual slabs
when the old period is too large.
On actual slabs (11) remains exact
but the periodic estimates cannot
be substituted without a transfer
theorem. No proof of the
recycled-history estimate or
the full fixed-time mean-gain
saving is obtained.

## 8. Reproducible audits

All three scripts were executed in the ECMAScript research runtime,
fetched at the exact remote commits and re-executed with identical
output. Reproduce with node. No separate Node or Lean invocation.
The weighted inequalities (5)-(10) above are paper-level deductions
from the previously checked bounded bridge and the displayed
Cauchy arguments; the audits check the renewal, bridge, short
injectivity, exact energies and finite ledger, not an asymptotic
estimate of Lambda_p.

A. research/min_local_negative_fresh_prime_excursion_energy_audit.mjs
   commit 02ca1aeb69178c4bb33d74113cca2605cce9d803
   blob 9e6e6f43534a611f2a3b1cd9a1f13382c02c31c9

For p=11,13,17,19 calculate all old root classes,
all activated low-period source nodes, and their
old reset excursions. Resolve the complete
renewal graph including zero-mass nodes.
Check (3), no cycles, terminal conditions,
old-exit refinement and exact mass-energy
reconstruction. Direct full-period comparison
for p<=17; deterministic root subsample
(step 97) at p=19, not full enlarged-period
enumeration there.

    old root classes                     181020
    old even-exit controls                 51825
    activated nodes                        271530
    reset excursions                       271530
    repeated fresh edges                      128
    renewal chain controls                 271530
    direct lifted root comparisons          214283
    complete enlarged-period roots         180950
    energy checks                           542854

All checks passed. All 128 repeat edges
are in the p=19 graph, with maximum chain
length two, but the positive initial
old masses at these repeating sources
are zero in this control. No assertion
of absence of positive-mass repeats in
general is made; audit B finds them.

    p   K2 at b    old exit K2   new exit K2  fresh increment
    11  1.00000      1.20000       1.34545      .14545
    13  1.34545      1.54805       1.65395      .10589
    17  1.83277      1.97083       2.12981      .15898
    19  2.12981      2.29684       2.39145      .09460

For p<=19 the positive-mass activated
sources in these complete old-period
profiles all have distinct terminal
lifts, hence B_p=0. This is a finite
observation, not a general injection.

B. research/min_local_negative_fresh_excursion_tail_audit.mjs
   commit 79b7d2eba719133427dd6857ad89ec19a6c38892
   blob df3a285a51742ceeff3af9742902c845b5811ccb

Three actual slabs R=48000,192000,480000,
six primes p=23,47,97,193,389,769 each.
For every canonical root independently
simulate old and new first b+1 cuts.
Reconstruct the new profile by renewal,
check the height-zero bridge and compare
the canonical seed's old exit to the
reset excursion. Split short and long
sources, compare exact root lists by
their terminal key and the energy
decomposition. These physical tests
do not assume uniform p residues or
apply the periodic 1/p normalized
bounds to the finite slabs.

    root/prime controls                     720018
    direct root predictions                  720018
    activated positive-mass sources            1960
    bridge comparisons                          1962
    repeated fresh checks                          2
    short injectivity controls                  1697
    endpoint mass/energy checks                 152612

All checks passed. The repeat occurs at
p=23 in two slabs (one root in the
smaller, two in the larger). Short
and long arrivals can share a terminal
key: the mixed collision energy is
18 and 40 respectively in those slabs.
This is a concrete failure of treating
all activated arrivals as disjoint,
despite the exact short-only injection.
The finite tests had no two long
positive-mass sources merging, but
that is not assumed in (9)-(10).

For R=480000 (80001 roots):

    p    old cut K2   new cut K2    short mass   long mass
     23    2.73953       2.86555        1643        219
     47    5.69264       5.80431         682        113
     97   10.79123      10.91390         427         73
    193   18.46488      18.55103         116         73
    389   31.01985      31.13802          96         33
    769   51.25582      51.30302          38          0

The high-p activated counts are small
and not estimates of the formal
conditional activation law.

C. research/min_local_negative_all_height_fresh_old_energy_audit.mjs
   commit 6c07fd0f80199de7c253c5dde0915247db2a428e
   blob 122420697d1c1fa1b7d7f9c4b5733b3a78685c9c

All canonical roots in R=48000,192000,480000.
Use the common cohort attaining first preheight
Hmax+1 by T=ceil(8 sqrt(2R+1)); Hmax=256 for the
first slab, 512 for the two larger ones.
Every root attains that cut in these controls.
Store first-record intervals, apply sparse
fresh corrections, verify mass conservation
and nonnegative old and fresh increments
at every height. Independent old-only
restricted replay at a deterministic
subsample of root/height pairs checks the
correction identity.

    roots                                120003
    surviving roots                       120003
    completed events                     2527603
    first-record intervals                654993
    root fresh corrections                 65077
    fresh-level controls                     429
    energy-increment controls               1271
    mass conservation controls              1274
    independent restricted replays          1905

All assertions passed.

    R        max preheight   E/N       fresh increase/N   old increase/N
     48000         257      38.54856        7.86702           29.68154
    192000         513      61.96784       13.16703           47.80082
    480000         513      60.19414       15.81420           43.37993

Initial normalized energy one. Fractions of
the increase assigned to fresh primes:
.20952, .21597, .26716.

For R=480000, at actual first preheight b+1:

    b        E/N       (E/N)/log^2(b+1)
     8      2.12921         .44103
    16      3.98226         .49610
    32      7.65672         .62629
    64     13.79014         .79138
   128     23.01552         .97450
   256     38.03864        1.23533
   512     60.19414        1.54578

This is a finite diagnostic of (11), not a
limiting growth rate or a counterexample
to a big-O assertion.

## 9. Next proof target

The first-b to first-(b+1) transition now
separates into a genuine old-only transfer
and an exact complete fresh insertion.
For the latter, the rare long reset
sources are characterized by old canonical
gain tails and the incoming energy is
bounded by the explicit weighted
displacement moment Lambda_p.
The dominant old transport still needs
an aggregate bound across all record
levels, including composite heights.
A sufficient approach to fresh transport
would bound A_p and B_p directly rather
than assume the K_3 and Lambda_p estimates
close (10). For old transport one must
handle repeated visits to the same
record level: its finite return map is
a decreasing spatial forest, but its
fiber weights need a new estimate.
This work does not show C(H)<<R log^2 H
at arbitrary heights, nor an actual
mean gain <T/3. Twin infinitude and
Lean formalization remain open.
No canonical Lean targets, sibling
branches or Context files changed.
