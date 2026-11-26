# Negative MIN: synchronized first crossings, launch-tail law, and canonical reset mixing

2026-11-27 JST. Continuation of 6566a18ff469f926870ec053e63f2afdedd7d66f.
The requested route is the ACTUAL fixed-time cohort gain, with first
crossings of gain scales rather than a near-square-root lower sieve.
We obtain an exact local multiplicity formula for large first-crossing
events, an unconditional weighted band bound, a relative asymptotic
for the entire large-launch tail at subpower thresholds, and a
coherent local trace transfer (including joint first-crossing moments).
One eighth of the large-launch tail gives canonical height-3 resets;
for fixed residue moduli the reset law is a convolution with uniform
units, providing a concrete but limited mixing mechanism.
The contribution up to the first polylogarithmic gain crossing is
o(T) in the actual square-root horizon. The subsequent gain remains
uncontrolled. These are paper-level deductions, not Lean verification,
not a claim of literature priority, and not a proof of twin infinitude.

## 1. Domain, first gain crossing, and exact synchronization

Use the actual canonical roots A in [R,2R], 6|A, h=3,
n_A=3-A/2. Set T=ceil(8 sqrt(2R+1)).
The previous height-local rule gives G_t<=2t+6, p<=2t+7
at each completed firing through t. Throughout this
horizon a>=R-O(T)>0 and n<0 for large R, so all
physical clock identities apply without a terminal cutoff.

For an integer J>=6 let tau_J(A) be the first elapsed
tick at which completed gain exceeds J, or infinity
if not attained in the horizon. The crossing event
has label p, previous gain g<=J, and source a=A-g.
Write h_arr for its source arrival height.
By the mod-30 potential of 2021e5a,

    h_arr <= 11+7g/4,
    W_arr <= floor(9g/4+8).

Define a large launch by

    p >= 64(J+1).                               (1)

The pre-firing height of a label p is at least
(p-1)/2, by the height-factor rule. Thus

    w >= (p-1)/2-11-7J/4 >= p/4.

Since the wait is at most twice either neighbor's
least prime factor, q(a)=min(P^-(a-1),P^-(a+1))
satisfies

    q(a)>=p/8 >=8(J+1)>Z_J,
    Z_J=2 floor(9J/4+8)+7.

The strict inequality uses J>=6. In particular
a is divisible by six. Every possible clock at a
has preheight >=(q(a)-1)/2 > 11+7J/4.
Therefore all canonical roots A=a+g with 0<=g<=J
which reach a have arrived before the first possible
clock after canonical birth at height 3. They all
share that single physical firing key (a,n).

Conversely, for any canonical source a whose first
clock from h=3 has large label p as in (1), the same
roughness conclusion holds, either by comparing
the stationary wait or the bound just proved with
g=0. Every root A=a+g, g a nonnegative multiple of
six <=J, which reaches a must have followed the
exact local arrival simulation of 8d83274 / 574a789:
it reaches by T_g=floor(9g/4+8) using primes <=Z_J.
Its next event is this very clock, and it crosses J
for the first time there (p-1>J). Monotone gain
ensures that no earlier crossing is possible.

Let h_e be the PRE-firing height of the stationary
clock. If the event must complete by elapsed T,
the root of offset g has elapsed firing time

    tau_J=h_e+g/2-3.

Thus the first-crossing multiplicity at this key is
exactly

    m_e(J,T)=sum_(0<=g<=J,6|g)
         1{a+g in [R,2R]}
         1{a+g reaches a by T_g}
         1{h_e+g/2-3<=T}.                       (2)

Write b_J(a) for the untruncated local profile on
Z_J-rough canonical a. Equation (2) is a precise
formula for all event depths, not merely a maximum
degree estimate. In particular m_e<=b_J(a). There
is at most one such key per source. If the source
is interior and h_e<=T+3-J/2, equality holds.
This avoids the error of assigning the same elapsed
wait to different participating roots; the absolute
clock is common but their birth and arrival times
can differ.

## 2. Static launch certificate and its product

Let epsilon=a/2 mod2. For p>=7 sufficiently large
(and in particular for (1)), the first minus clock
at a canonical stationary source with p|a+1 has
preheight

    (p-1)/2   or   (3p-1)/2.

For plus with p|a-1 it has preheight

    (p+5)/2   or   (3p+5)/2.

In each case the shorter representative occurs
precisely when p==a+1 mod4 (equivalently
p==2 epsilon+1 mod4). Indeed a/2 mod p
is (p-1)/2 on the minus side or (p+1)/2
on the plus side, and the fixed parity determines
its lift mod 2p. Apply the respective absolute
clock n=0 or p+2 mod2p and take the first height
strictly above 3. The two representatives displayed
above are above 3 in the large-label range.

For fixed parity, label p and side, the pin
a== -1 or +1 mod p determines its exact clock
height h_e. For each other prime q the two spatial
residues a==-1,+1 mod q have predetermined first
clock heights above 3. Deny a residue if its clock
would precede h_e, or tie at h_e with q<p.
For q small (including 5 or 7) always use the first
strictly positive wait from h=3, not a possibly
nonpositive short representative. This is the exact
certificate that the pinned p wins the stationary
race, and has at most two denied residues per q.
There is no extra independent condition on p;
its other sign residue is already excluded by
the pin. The canonical coordinate at 3 is zero.

All q<=p/8 (q>=5) have both residues denied:
their first opportunity is <=3+2q<h_e for large p.
No q>4p+10 can be relevant, since its minimal
preheight exceeds h_e. In particular all q<=Z_J
are denied under (1), either by these bounds
or the synchronization argument. Let

    V(u)=prod_(5<=q<=u)(1-2/q),
    V(p^-)=prod_(5<=q<p)(1-2/q).

The free-prime survivor product above Z_J,
excluding p, is

    V_free(p,epsilon,side)
       = [V(p^-)/V(Z_J)] (1+O(1/log p)).         (3)

This follows because the possible discrepancy in
the factors is confined to a constant-ratio band
[p/8,4p+10], whose prime reciprocal sum is
O(1/log p). The estimate is uniform in the
four clock choices and in J satisfying (1).
In particular no assumption about independence
of the dynamically chosen low path is made.

## 3. Unconditional actual band moments

Fix a positive integer r. Take

    X=log R, l=log X,
    6<=J<=c_r X^2/l,                            (4)

where c_r is a sufficiently small constant,
as in the adaptive local-moment transfer of 574a789.
It may be reduced by absolute factors below.
Write mu_r(J) for its exact formal conditional
local moment; in particular

    1<=mu_1(J)<=1/V(J+1)<<log^2(J+2),
    mu_r(J)<=(floor(J/6)+1)^(r-1) mu_1(J).

For the actual slab let

    E_r(J;I)=sum_(first crossing keys e,
                 p_e in I, tau<=T) m_e(J,T)^r.

For r=1 this is root mass, for r=2 it is
the quadratic energy of just those first crossings.
The keys are grouped by physical source and firing
tick, not by elapsed time.

For Y>=64(J+1), Y<=2T+7, a large launch with label
p in [Y,2Y) has p|a+1 or p|a-1 and a is p/8-rough.
By (2), majorize its energy/mass by b_J(a)^r.
For a fixed p and sign, apply exactly the adaptive
local transcript upper sieve of 574a789 sections
2-6, with the following modifications:
* a is a source rather than a final semiprime center;
  the additional progression pin is p|a+/-1;
* p>Z_J, so the pin is coprime to all local
  small coordinates and positively pinned primes;
* require both neighbor residues absent at free
  primes Z_J<q<=min(p/8,R^xi), for small fixed xi>0.
  This cutoff is above Z_J. Its log is comparable
  to log p since p<=2T+7=O(sqrt R).

For each accepting local transcript the main term
uses the factor 1/p and the free product
O(1/[V(Z_J) log^2 p]). The exact normalization
of local accepting weights is V(Z_J) mu_r(J).
Consequently the per-prime per-side main bound is

    << R mu_r(J)/(p log^2 p).

For clarity on uniformity: use the same small modulus
M0<=R^u, u=1/100, medium pin product <=R^u,
number of leaves per tuple and small class <=R^u,
and combined divisor support <=R^(2u+o(1))
as in 574a789. There are polylogarithmically many
offset tuples. The extra p modulus is coprime to
every expanded divisor. The summed CRT remainder,
even over all p<=2T+7, is R^(1/2+6u+o(1)).
It is negligible compared with R mu_r(J)/log^3 R.
The additive medium main-term errors are summed
with 1/P pin weights as in that note, and are
exp(-Omega(X/l)) times the relevant progression
lengths, negligible uniformly in the band. For
J so small that the medium block is empty the
corresponding medium error is exactly zero.
The expanded boundary [R-J,2R] instead of [R,2R]
does not affect the bound.

Use sum_(Y<=p<2Y)1/p <<1/log Y. This yields

    E_r(J;[Y,2Y)) <<_r R mu_r(J)/log^3 Y.       (5)

The proof uses only an upper sieve in actual
integer progressions; it does not require an
unproved uniform merger-energy bound or a
lower sieve near sqrt R.

For every fixed theta>0, summing dyadic bands
up to 2T+7 gives

    E_r(J;[R^theta,infinity)) <<_(r,theta)
                                  R mu_r(J)/log^2 R.           (6)

If a threshold exceeds the physical label bound
the corresponding mass is simply zero.
For r=1 (6) is O(R l^2/X^2)=o(R).
For r=2, at the maximal budget (4),
mu_2(J)<< (J+1)log^2(J+2)<<X^2 l,
so (6) is O(R l). In a single square-root
constant-ratio band (5) is sharper:

    E_1 << R l^2/X^3,
    E_2 << R l/X=o(R).                          (7)

These are unrestricted-event-depth estimates on
the first crossings out of the polylogarithmic
gain budget. They do NOT bound the same labels
on the portion of a path after its first crossing.

## 4. Relative actual launch-tail asymptotic at subpower thresholds

A stronger result holds away from the square-root
threshold. Assume (4) and

    Y>=64(J+1), Y->infinity, log Y=o(log R).     (8)

Put Y'=exp(sqrt(log Y log R)), rounding the
thresholds harmlessly. Then log Y'/log Y->infinity,
log Y'=o(log R), and Y'=o(T). Every stationary
first crossing with p<=Y' completes by elapsed
2p+J/2+O(1)<T for sufficiently large R. Hence
(2) equals the whole local profile, away from the
slab boundary. Its boundary error summed across
all these labels is O((J+1)^(r+1)), since each
source has a unique stationary winner.

For p in [Y,Y'], count the EXACT stationary
certificate of section 2 rather than just
p/8-roughness. Use both upper and lower block
polynomials of 574a789, with free primes extending
to 4Y'+10. The free cutoff is subpower, so the
block order parameter may tend to infinity with
divisor support still <=R^(2u+o(1)). Thus the
relative free main-term error is o(1) uniformly.
The medium additive error remains exponentially
small after reciprocal pin weights; the number
of added p choices is R^o(1), and all CRT errors
sum to R^(6u+o(1)). These are negligible even
against R/log^2 R. We obtain, after summing local
class and transcript weights, the main term for
one p and one sign:

    (R/6) mu_r(J) V(p^-)/p.

More precisely the combined errors are o of the
summed main term on the whole interval, with a
uniform relative O(1/log Y)+o(1) free-product
error and negligible additive errors. This
assertion does not depend on the local mean
moments being bounded: they are at least one,
and all weights are nonnegative.

Since

    V(p^-)-V(p) = 2 V(p^-)/p,

summing both signs telescopes to
V(Y^-) minus V(Y') (with endpoint rounding).
The difference is asymptotic to V(Y) by Mertens.
For the remaining p>Y' use (5) and sum dyadic
bands to bound the tail by O(R mu_r(J)/log^2 Y'),
which is o(R mu_r(J)V(Y)).
Therefore

    E_r(J;[Y,infinity)) ~ (R/6) mu_r(J) V(Y).    (9)

This is an actual-integer asymptotic for large
first-crossing keys, including their r-th
multiplicity moment. The admissible J may grow
through (4), and Y may grow through (8).
It uses the square-root horizon only as an
upper horizon that is long enough to include
all subpower first crossings. It is not a lower
sieve at a square-root prime threshold.
The first moment (r=1) is a genuine lower and
upper count for this subpower launch population.
The same result is valid for prescribed fixed
source parity/residue conditions with the
corresponding restricted local moment in the
main term (additive errors negligible relative
to the total unrestricted main term).

Formal analogue: on independent uniform root
coordinates, every finite displacement has
some eligible odd prime almost surely, because
the product V(y) tends to zero. Taking the
countable intersection over possible positions,
the full formal path eventually crosses each
fixed finite J almost surely. For a source
a=A-g, fixed 6|g<=J, root coordinates translated
to the source are again uniform canonical
coordinates. Formula (2) without the time
or slab cutoff holds for its formal local hits.
For large p, the pin costs 1/p and the independent
free product is (3). Sum over g and both signs,
using exact conditional local normalization.
Consequently

    Pr_formal(p_(tau_J)>=Y)
            =(1+O(1/log Y)) mu_1(J) V(Y)        (10)

uniformly for Y>=64(J+1), Y large.
No finite-slab transfer is used for (10).
The telescoping proof includes the whole infinite
tail, since V tends to zero. In particular for
Y=J^alpha, alpha>1 fixed, as J->infinity its
main term is (alpha^-2+o(1)) V(J+1)mu_1(J).
If the conjectural local saturation holds this
gives an inverse-square law on the logarithmic
scale of the first-crossing label. Saturation
itself has not been established.

## 5. Local coherent trace transfer and small-crossing moments

The adaptive CRT argument is not specific to
local arrivals at rough centers. For fixed r,
consider r canonical roots A+d_i, with fixed
even multiples of six d_i (not random
independent roots), over an anchor interval
of length comparable to R. Simulate all r
up to a common elapsed horizon Q, where

    Q<=c'_r X^2/l.

The physical slab is assumed at scale R and
the offsets O(Q), so these paths remain in
the negative-time physical regime. At each
tick only primes <=2Q+7 are relevant. Take
z=kappa0 X as in 574a789. Once the small
coordinates and anchor parity are fixed,
the height factor integer has at most one
prime factor >z, since 2Q+7<z^2.
A previously unknown medium positive test
pins an anchor coordinate and consumes >z-1
gain on its particular root. The r roots
together have gain <=r(2Q+6). Thus the total
pins, pin product, number of possible positive
test slots and leaves are bounded by the
same R^u caps as in 574a789, on taking c'_r
small enough. The roots share their known pins
and denied sets, preserving correlations.
No endpoint roughness is required in this
argument, and medium coordinates can start
with their entire residue sets.

For any selection of complete traces, the
medium forbidden-density sum is <=r Q/z
and the sum of reciprocal positive pin
products over leaves is <=exp(r Q/z).
The single medium Bonferroni block in
574a789 suffices. Its main-term additive
errors sum to exp(-Omega(X/l)); its
per-leaf absolute CRT remainder with
support <=R^(u+o(1)) sums over all leaves
and low classes to R^(4u+o(1)).
After dividing by the number of anchors,
for every subset of possible trace tuples
the empirical probability differs from
the coherent formal product probability by

    O(exp(-c X/l)+R^(-1/2)).                    (11)

The constants depend on fixed r and cutoff
constants, not on the selected event set
or allowed fixed offsets. Equivalently this
is a total variation estimate on finite
coherent trace tuples (the supremum over
all selections). It uses the genuine
single-anchor CRT law, not a replacement
by independent trajectories. When all
primes are small the exact progression
count gives the corresponding bound
without a medium block.

Here is an immediate application to
first-crossing energy. If p<64(J+1),
a first crossing of J ends with gain
<=J+64(J+1) and elapsed time
<=9(J+64(J+1))/4+8. This is O(J).
Shrink c_r in (4) to apply (11) through
this horizon. For r ordered roots sharing
a first-crossing key their previous gains
all lie in [0,J], hence the roots differ
by at most J. Anchor the smallest root
A_0 and enumerate ordered offsets
d=(d_1,...,d_r), 6|d_i, 0<=d_i<=J,
min_i d_i=0. There is one anchor per
ordered tuple even if it includes
repeated roots. Let B_d be the formal
event that all these roots have small
first-crossing label and the same
physical firing key. In relative
coordinates the equality tests are
d_i-g_i constant and t_i-d_i/2 constant
across i, where g_i is pre-crossing gain,
t_i is elapsed firing time.
All these tests are functions of the
coherent local trace tuples.

Equation (11) and the O((J+1)^r) choices
of offsets, including boundary truncation
of the anchor interval by max d_i, give

    E_r(J;[0,64(J+1)))
       = (R/6) sum_d Pr_formal(B_d) + o(R).     (12)

For r=1 this is the short-horizon small
first-crossing population. For r=2 it
is an explicit coherent formal pair
moment, not a product of marginal hit
probabilities. Equation (12) gives a
local initial condition for a prospective
multi-scale merger recursion. The sum
of formal pair probabilities as J grows
has not been bounded beyond the obvious
multiplicity bounds in this note.
No comparable trace transfer is proved
at a polynomial horizon or gain budget.

## 6. First crossing law including its entire prior history

One can extend the r=1 trace transfer
beyond the local horizon, provided the
gain crossing threshold remains (4).
For large p in [64(J+1),Y0] with
Y0=exp((loglog R)^2), use (2) and
the exact stationary certificate.
For each offset g, source residue class
and accepting local arrival transcript,
record the entire ordered prefix from
A=a+g to a (including all elapsed waits
and sides). It is determined by the
transcript, since each tick's winner
is known. The final p pin and side
determine its stationary preheight,
hence its final wait and elapsed
crossing time. For arbitrary selected
sets of such full histories, the
certificates are disjoint for a
given initial root: it has only one
first-crossing key, pre-gain, and
complete local arrival trace. Count
each using the local transcript and
exact free block polynomials, just as
in section 4. There are only polylog
many offsets and R^o(1) p choices;
the reciprocal-pin weighted medium
error and the summed CRT error
remain negligible. The relative
free-sieve error times the summed
formal probability is o(1), since
that summed probability is at most
one. Thus the normalized actual
probability and formal probability
differ by o(1), uniformly over any
selection of histories with p<=Y0.
Small-p histories use (11) instead.

By (10) the formal mass of p>Y0
is O(mu_1(J)/log^2 Y0)=O(l^-2).
All p<=Y0 crossings complete by
O(J+Y0)=R^o(1)<T. The uniform
probability transfer for that
population implies the total actual
remaining mass (including roots
not crossing by T) is o(1).
This proves a total variation o(1)
transfer for the ENTIRE relative
first-crossing history, with a
separate cemetery value on the
actual side if no crossing occurs
by T. It is valid at the physical
square-root horizon, but only for
this stopped gain threshold.
In particular

    Pr_R(tau_J<=O(J+Y0), p_(tau_J)<=Y0) ->1.    (13)

The implied fixed constant in the
time bound follows from the mod-30
potential, not a tail bound on all
possible incomplete waits.

This is a genuine actual-to-formal
transfer of an initial stopped path
with a potentially much longer time
than its local gain budget. It does
not transfer the post-crossing
distribution conditional on that
history to a new independent
canonical environment.

## 7. Phase decomposition and a fixed-modulus mixing lemma

The large-launch preheight formula
in section 2 gives exact postheight

    0 or p   (minus),
    3 or p+3 (plus).                            (14)

Call the first option on each side
short, the second long. For a fixed
source parity, the short primes
occupy one of the two reduced
classes mod4. Because the product
(3) is asymptotically the same
for both sides and parities,
the ordinary prime number theorem
in FIXED arithmetic progressions
implies each of these four launch
types contributes asymptotically
one quarter of (9) (for any fixed r).
To see this in the weighted sum,
on dyadic prime bands V(p^-) differs
from the band's starting V by a
relative O(1/log p); use partial
summation and fixed-modulus PNT
to split the weighted reciprocal
prime sum in equal proportions
among its reduced classes. The
relative error is uniform over
all bands starting above Y as
Y->infinity. The upper tail
p>Y' in the actual count is
negligible as before.

Of particular interest are the
PLUS short launches with p==1 mod3.
Then the arrival B=a-p+1 is a
multiple of six and has h=3,
exactly a new canonical seed.
Its absolute tick is odd, so B/2
is even and B is divisible by 12.
This conclusion does not require
a subsequent bridge. On each fixed
source parity the condition is
one of the four reduced classes
mod12, and only one of the two
sides. Therefore these exact
canonical resets contribute

    (1/8+o(1)) E_r(J;[Y,infinity))              (15)

to the large-launch mass/energy
of (9), for (8). The other short
reset types can use the finite
bridge in 5b148fe when applicable,
but (15) only counts direct
canonical height-3 resets.

There is a precise limited mixing
property of the new seed B.
Fix a squarefree M with prime
divisors q>=5, independent of R
and J. In the adaptive count for
(9), prescribe the source residue
vector modulo M (eventually these
primes are included among the fixed
small coordinates). Let rho be
the normalized law of that vector
weighted by b_J(a)^r conditional
on Z_J-roughness; the source parity
may be fixed first and then averaged.
If M contains a prime >Z_J in the
small-J case, include it among the
fixed low coordinates and condition
it rough as well: every p>=Y
event forces it for sufficiently
large R; the enlarged local
normalization still equals the
original one after summing the
finite extra rough coordinates.
This defines rho also when J is
fixed. The p mod12 restriction in
(15) and any unit p mod M are
coprime conditions. Fixed-modulus
PNT, the uniform free product (3)
and the restricted local weights
show that p mod M is asymptotically
uniform over units, independently
of the source vector, within this
canonical reset population. Formally
the joint law is within o(1) in TV
of the product of rho and uniform
units. This holds even if rho changes
with J: there are finitely many
classes, and the summed additive
sieve errors are negligible against
the total positive weight.

The new seed satisfies B=a-p+1.
Thus, up to o(1) in TV, its residue
distribution mod M is the convolution
of rho (shifted by one) with uniform
units (negated). In particular, for
each q|M and residue x,

    Pr(B==x mod q)
          = [1-rho_q(x-1)]/(q-1)+o(1).         (16)

Uniform units have total variation
distance 1/q from uniform residues
at a prime q. Coupling independently
at all q|M gives

    TV(law(B mod M), uniform mod M)
                     <=sum_(q|M)1/q+o(1).      (17)

No assumption of a uniform source
distribution is needed here. More
precisely for a nontrivial character
of the product residue group with
active coordinates S, the absolute
Fourier coefficient is reduced
by factor prod_(q in S)1/(q-1)
relative to that of rho (up to o(1)).
This follows directly by summing
a nontrivial additive character over
the q-1 nonzero residues. The phase
from shifting by one has modulus one.

This is a concrete reset mixing
mechanism even under mass/energy
biased source laws. It does NOT
give uniformity modulo growing M:
both the fixed-AP theorem and the
sieve estimates here are used
with M fixed. The new seed also
has fixed half-distance parity,
and the full prior history can
contain correlations with large
prime coordinates. Thus (16)-(17)
cannot justify independently
restarting the full MIN at each
successive launch.

## 8. Consequence for actual fixed-time gain

Stop each root at the first completed
crossing of J, or at T if there is no
crossing. Denote the stopped gain by
G_stop. If p<64(J+1), or the crossing
does not happen, G_stop=O(J+1).
For the remaining crossings use
(5) with r=1. The summed jump gain
on a dyadic band is <=2Y times
E_1(J;[Y,2Y)). The elementary
geometric sum up to 2T+7 obeys

    sum_dyadic Y/log^3 Y << T/log^3 T

for T large compared with J and
Y>=64(J+1): split at sqrt T, then
sum the geometric weights above
sqrt T. Thus

    E_R[G_stop] << J+1+
                       T mu_1(J)/log^3 T
                << J+1+T l^2/X^3 =o(T).        (18)

This is an unconditional actual
initial-stage gain bound, including
large early jumps. It does not
use a conjecture about the full
cohort energy. Also (13) implies
E_R[min(tau_J,T)]=o(T), because the
exceptional proportion tends to zero
and the other crossings occur by
R^o(1). These conclusions use
different bounds (18 controls gain,
(13) controls stopping time).

Under the hypothetical finiteness
of twins, d9f6049 gives G_T(A)>=
(1/3-o(1))T uniformly on large slabs.
Hence all roots cross J by T,
and by (18) the post-crossing
gain must still satisfy

    E_R[G_T-G_stop] >= (1/3-o(1))T.             (19)

Moreover almost every such root
has reached its first crossing
at a subpower label/time by (13).
Thus a direct launch from the local
budget to a polynomial-size prime
cannot supply the hypothetical
necessary gain. A proof along the
demand/supply route must estimate
the subsequent gain accumulation,
not just the initial waiting law.
A sufficient target is a strict
mean saving below T/3 for this
post-crossing gain along unbounded R.
A multi-scale estimate must retain
the mass and the history of the
earlier crossings. Neither the
canonical resets (15) nor their
fixed-modulus mixing (17) alone
gives that estimate. In particular
there is no legitimate iteration
of (5) beyond (4) using a fresh
unconditional local profile.

## 9. Executed reproducible audits

A. research/min_local_negative_first_crossing_launch_audit.mjs
   commit 6ac556d72f201fb4262efa8b4217e964cc19470a
   blob b935831a69a2587068ad58438342002a64e95f08

Executed in ECMAScript research runtime, fetched at the exact
remote commit and re-executed with identical output.
Reproduce with node. No separate Node or Lean invocation.
All canonical roots in five slabs R=12000,48000,192000,
480000,1000000; five budgets J=6,12,24,48,96 at each.
Enumerate forward events to the first crossing even if it
lies after T (the first crossing is before terminal zero),
and compute full gain at T independently of the crossing.
For every large launch with p>=64(J+1), including those
after T, group by source and compare stationary clock,
roughness, postheight, and the actual root list to the
independent height-local simulation of every local offset.
Compare also the time-filtered root list exactly. This
includes launches to terminal large prime labels beyond
the physical square-root horizon; the timed counts separate
those cases. The finite control uses all roots, not just
a sample. The five budgets repeat the same roots.

    root/budget controls                1443355
    completed event computations       42759235
    first crossings within T            1250520
    large launches (even after T)        207341
    large launches within T               14506
    roughness / stationary key / phase
      checks (each)                       207341
    distinct source/budget controls       70326
    local offset hit checks               466638
    exact full root-list comparisons       70326
    exact timed root-list comparisons      70326
    canonical direct reset checks           2675

The initial scratch check failed on a root list:
the inner factor sieve overwrote smaller factors,
so the independent height-local reference did not
choose the least prime at a simultaneous clock.
After fixing it to preserve the least factor,
all final comparisons passed. No incorrect scratch
script was committed.

Example R=1000000 (166667 canonical roots,
T=ceil(8sqrt(2000001))=11314), with full mean
gain 1221.92975214 for each budget:

    J   crossed by T   large by T   large energy    mean G_stop
     6     155650         6754          12026         71.9814
    12     153007         3304           7700         89.4300
    24     147977          697           2417        122.6519
    48     141204            0              0        168.2600
    96     131316            0              0        236.6808

The large threshold is deliberately generous for
synchronization; the last two finite timed controls
have no large launch. Many beyond-T large launches
are at twin centers, so not physical gain events
inside the square-root horizon. The actual formula
(2) and (14) were nevertheless tested on both.
These finite budgets and slabs do not test the
asymptotic power/log thresholds in (4),(8).

Independent stationary clock controls: 16 fixed
label/parity/side cases, 24600 direct period scans
confirming the first heights and the finite
forbidden-residue lists. Four finite convolution
controls with arbitrary positive nonuniform
rough-source weights and 47 marginal identities,
checking (16) and (17) by direct enumeration.

B. research/min_local_negative_stationary_race_tail_audit.mjs
   commit e335aa394cd7ec22f6ff21aba20bcd217180c301
   blob c938d51c95e57921a41699ee8243a3fb93058f32

Executed, fetched at the exact remote commit and
re-executed with identical output. For two rough
cutoffs Z=50,200 and each parity, enumerate all
first clock opportunities above Z up to prime
cutoff 8000000. Sort by (height,label).
Starting with survival one, at an opportunity
for p with k already denied residues, its
conditional match probability is 1/(p-k);
subtract that probability times current
survival. This is an exact finite probability
recursion, evaluated in floating point, not
a rational-arithmetic enumeration of all
environments. The event weights for p<=2000000
include every possible earlier competing clock
because all required labels are below 4p+10.
Check four total probability conservation
identities and independently calculate 32
selected event probabilities directly as
products over denied residues. All matched.

    stationary clock evaluations         4317972
    finite tail comparisons                   14
    residue-class diagnostics                140

For Z=200, odd half-distance parity, labels
in [1000000,2000000], the exact-formula
probability is .0143463496366, and the
telescoping main-term prediction is
.0142618438691 (ratio 1.00592530).
Short fraction .53825345, plus fraction
.49999993, direct canonical reset fraction
.13432863 (compare their asymptotic limits
1/2,1/2,1/8). Conditional on a canonical
reset in this formal race, p mod5's four
unit proportions are .24877,.25006,.25142,
.24975; the six p mod7 unit proportions
are within .002 of 1/6. These are finite
product-rule diagnostics, not a proof of
PNT in AP or an empirical test of (9)
on actual near-square-root slabs.

No new direct exhaustive test of the
adaptive trace/block sieve asymptotic
in (9),(11)-(12) was run: those are
extensions of the previously audited
block-polynomial and local-transcript
argument of 574a789, as spelled out above.
The present independent controls test
the required local characterization,
stationary clock race, phase and convolution
identities. No canonical Lean target,
sibling branch, or Context files changed.

## 10. Remaining proof

The first-crossing strategy now has an
unconditional large-label supply bound (5),
a sharper actual subpower tail asymptotic (9)
including merger moments, local coherent
pair data (12), and stopped-history transfer
(13). Direct canonical resets give a
fixed-modulus smoothing law (17).
The full initial-stage contribution is
o(T) by (18), without assumptions on
merger energy. The hoped-for actual
mean upper bound <T/3 is not proved:
after leaving the polylogarithmic
gain budget, the conditional root
population and its long histories
need a new scale-to-scale estimate.
The finite-coordinate mixing lemma
does not yet supply it. No proof of
twin infinitude, no Lean verification.
