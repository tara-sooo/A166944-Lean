# Negative MIN: event gain barrier, dyadic rigidity and survival of distinct sections

2026-11-27 JST. Continuation of 5b148fe4380f20eceb76d5377f7f891e90419fa8.
Test the proposed height-doubling route. A universal gain barrier
shows that a successful low-budget upper section cannot contain
any new event since the preceding half-height section. An exact
stationary filter replaces this part of the adaptive transport.
A fixed-dimension upper sieve bounds distinct lost states per
doubling, giving a quantitative conditional scale-lifting theorem
and an unconditional small-exponent extension from the previous
lower-sieve construction. The latter is not an extension beyond
the usual lower-sieve range. No square-root gain saving proved.

## 1. Universal gain barrier at a high firing

Start at a seed of height h0 in {3,6}. For a completed event,
let g be the accumulated full gain before the event, w its wait,
p its label, h_arr the height at the preceding completed
arrival (or seed), and b=h_arr+w its pre-firing height.
Let g_plus=g+p-1. By the universal mod-30 potential,

    h_arr=h0+W_pre-g/2 <=14+7g/4.

The preceding opportunity of this SAME eligible prime clock
is 2p ticks earlier than the actual firing. Since the event
wins at its first opportunity after the preceding arrival,

    b-2p <= h_arr <=14+7g/4.                     (1)

This is true even when other primes compete; the selected
prime is eligible at the unchanged spatial source throughout
its waiting interval.

The preheight satisfies p|(2b+1) for the minus clock and
p|(2b-5) for the plus clock. Split into two cases.

If p<=(2b+1)/5, (1) gives

    g_plus >= (4/7)b - p/7 - 9
           >= (18/35)b - 9 - 1/35.

If p>(2b+1)/5, then the relevant odd quotient is less than
5, so b<=(3p+5)/2. This also holds for the possible small
negative plus quotient. Consequently

    g_plus >= p-1 >= (2/3)b-8/3.

Both cases give the uniform inequality

    g_plus >= (18/35)b-10.                        (2)

No twin-free assumption, distribution hypothesis, or
specific alphabet cutoff is needed; only the ordinary
height update and the mod-30 inequality. This is not an
optimal-constant claim.

## 2. Exact fixed-budget section filter

For a canonical root (or phase-6 seed), let a_H and G_H
be its state and total gain at first POST-tick height H.
Require that the physical process stays in the slab
through the passage, or define success as reaching the
height before exceeding a specified gain budget. At a
first passage the tick is idle, since the height can
increase by at most 1 and a firing decreases the
preheight by at least 1. Thus the first passage is a
genuine state (a_H,n=H-a_H/2).

Take H2>H1>6 and a fixed full gain budget L satisfying

    L < (18/35)(H1+1)-10.                         (3)

If a root reaches H2 within budget L, it must have
reached H1 within budget L. If any event occurred after
first passage H1 but before first passage H2, the FIRST
such event has preheight at least H1+1, so (2) would
force the accumulated gain to exceed L. Hence no event
can occur in that interval.

Conversely a root that reaches H1 within L and whose
next wait at that section is greater than H2-H1 reaches
H2 with exactly the same position and gain. The
first-H2 event cannot fire on the target tick, so the
strict wait inequality is essential.

Let E(H,L) be the set of DISTINCT first-passage spatial
endpoints with total gain<=L, over a fixed set of initial
roots, all of height 3 or 6. In an initial slab [R,2R]
assume H2+L=o(R) so all successes and stationary extensions
are physical. Define w_H(a) as the ordinary next wait
starting from (a,H-a/2). Then (3) gives the exact identity

    E(H2,L)={a in E(H1,L): w_H1(a)>H2-H1}.       (4)

The identity also holds for each individual root and
for the entire multiplicity at every surviving endpoint.
No coalescence can be created among the surviving states
in this interval. Any first-passage state with a fixed
gain <=L is reached before the preheight can exceed
(35/18)(L+10); the later higher sections simply filter
these states by stationary survival.

In particular for H2=2H, L=H/2, (3) holds for every
H>=700. Therefore

    G_(2H)<=H/2  =>  a_(2H)=a_H, G_(2H)=G_H.     (5)

This does NOT say every root with G_H<=H/4 succeeds at
2H. It says every upper success is already at the same
endpoint at H, with the relaxed budget H/2. A root can
newly qualify at 2H simply because the budget doubled.
More generally H2=cH, L=lambda H2 with fixed c>1:
when lambda*c<18/35, (4) holds for all large H.
For doubling, the rigidity threshold is lambda<9/35,
strictly larger than the selected target 1/4.

The proposed incremental gain condition
G_H<=H/4 and G_(2H)-G_H<=H/4 therefore forces ZERO
additional gain for sufficiently large H. At that
budget, repeatedly allowing small new jumps in the
last half-height interval cannot generate new states.
A genuinely dynamic lifting step must occur below
the barrier, use a larger intermediate gain budget,
or use a different restart seed and explicitly
account for its new gain origin.

## 3. Unconditional loss bound for a doubling

Let H tend to infinity with H<=C sqrt R, for a fixed C,
and let a selected set of roots in [R,2R] have first
passage H with G_H<=lambda H for fixed 0<lambda<4/7.
They may be phase-3 or phase-6 seeds; count distinct
initial states if including both. Put D_H=#distinct
endpoints and denote their multiplicities by m_a.

At every such endpoint, the final idle duration from
the last arrival obeys

    I_H >= H-h0-7G_H/4-8
        >= (1-7lambda/4)H-14.

Since every eligible odd prime q has its next
opportunity within 2q ticks at that arrival, and
no firing occurred through the passage, each q
dividing a-1 or a+1 exceeds I_H/2. Thus both
neighbors are c_lambda H-rough for a fixed positive
c_lambda and all sufficiently large H. For lambda=1/4
one can retain the explicit cutoff 9H/32-7.

Consider the distinct endpoints a that fail to
remain stationary up to height J, H<J<=2H.
The first new event from (a,H-a/2) has a label p
with

    c_lambda H < p <= 2J+1 <=4H+1.

The source a stays fixed until that event. Count
possible a in [R-lambda H,2R] for each p and
direction: one neighbor pm, the other pm+/-2,
with m an integer in an interval of length O(R/p).
Here m is of scale R/p, and large compared with
a sufficiently small fixed power of H. Both m
and pm+/-2 must avoid all odd prime factors up
to z=H^epsilon for small fixed epsilon>0, because
a is c_lambda H-rough. The sifting primes are
distinct from p. The two prohibited residue
classes modulo each odd sifting prime are
distinct. Using the same standard two-dimensional
upper sieve as d9f6049 and 5b148fe, with level
sqrt(R/p) and CRT remainder <=2^omega(d),
gives the uniform bound

    O_lambda(R/(p log^2 H)).

Indeed R/p is bounded below by a fixed positive
multiple of H for H<=C sqrt R and p<=4H+1;
the level parameter is large at sufficiently
small epsilon and the summed remainder
O(sqrt(R/p) log(R/p)) is absorbed in the
main upper bound. Constants can depend on
lambda,C, not on the selected set or R,H.
Summing over primes in the constant-ratio band
uses Chebyshev's bound sum 1/p=O_lambda(1/log H).
Thus the number B_H of DISTINCT selected endpoints
at which any event occurs before or at J is

    B_H <<_(lambda,C) R/(log H)^3.               (6)

All other endpoints survive, with the exact same
gain and root multiplicities. For the expanding
budget lambda J, this proves

    D_J >= D_H - C_(lambda,C) R/log^3 H.         (7)

The inequality is valid regardless of whether
the roots with a new event later qualify.
It applies without (3); (3) adds the stronger
exact characterization for the expanded fixed
budget in (4). The bound (6) is unconditional
for the actual selected population; it does
not require spatial independence or a full
CRT period for prior event histories.

For a fixed selected cohort of size N_s and
energy C_s=sum m_a^2, the number of roots removed
if discarding all failing endpoints is

    N_lost <= sqrt(C_s B_H)
            << sqrt(C_s R/log^3 H).              (8)

For a surviving cohort, no stationary states
merge, so its energy never increases. Across
many stages, use Cauchy-Schwarz ONCE on the
union of the disjoint removed endpoint sets,
rather than summing root-loss bounds stage by
stage. This avoids an artificial accumulation
of square-root errors.

## 4. Scale lifting and its limits

Start at H0, double to H_m with the last ratio
allowed smaller than 2, all <=C sqrt R. Keep
only stationary survivors of the initial set
with G<=lambda H0. Their gain is unchanged
throughout, so they satisfy every later
low-gain budget. Summing (6) gives

    D_surv(H_m) >= D_0 - C1 R sum_(i<m) 1/log^3 H_i
      >= D_0 - C2 R [
          1/log^2 H0 - 1/log^2 H_m + 1/log^3 H0 ]. (9)

Here H_i=2^i H0 before the final partial step.
The last inequality follows by integral comparison
of the decreasing function (log H0+x log2)^(-3).
The constants depend only on fixed lambda,C.
The surviving mass loses at most the square root
of C_s times the entire distinct loss bound.

A useful local scale-extension theorem follows.
If D_0 >= c R/log^2 H0 for fixed c>0, there
is fixed delta>0 depending on c,lambda,C such
that lifting to H_m<=H0^(1+delta) (within the
square-root scale) preserves at least D_0/2
distinct endpoints for all sufficiently large H0.
Indeed at most (delta/log2)log H0+1 doublings
are needed, so (9)'s loss is O(delta R/log^2 H0
+ R/log^3 H0); choose delta after c and the
upper-bound constant. Gain stays <=lambda H0.
In particular an exponent alpha at which a
lower bound D_0 >> R/log^2 R is known can
be enlarged by a fixed factor 1+delta,
provided the constants and the ceiling on H
allow it.

There is an unconditional application at small
exponents. Use the explicit p=7 plus event
family j=55 mod154 from 74a6796, after which
a=6j-6 and h=3. The stationary lower sieve
in that note gives, for some sufficiently small
fixed alpha>0 and H0=floor(R^alpha), at least
c R/log^2 H0 actual roots with no additional
firing through first height H0. The roots
have gain 6 and their endpoints are distinct,
since a=A-6. Thus for sufficiently large R
all satisfy the lambda budget, e.g. lambda=1/4.
Apply the preceding scale-extension theorem.
For some fixed delta>0, the same initial word
has at least (c/2)R/log^2 H0 distinct survivors
at H_m=floor(R^(alpha(1+delta))) (reduce delta
if necessary so the ceiling is met), with
gain still 6. The endpoint time is H_m-3+3=H_m
relative to the initial seed. The application
uses the lower sieve only at the starting
height, and upper sieves for the extensions.

This is a rigorous bounded scale lift, but not
a result beyond the known small-exponent
lower-sieve range: no optimized alpha, delta,
or absolute maximum exponent is obtained.
In the starting example survival is itself a
static roughness/clock condition; a stronger
static lower sieve might yield the same or
more directly. One cannot iterate the theorem
indefinitely with a fixed delta without
tracking the surviving density constant c.
The accumulated bound (9) can be of the
same order as D_0 over a long polynomial
scale change. Its unspecified constants
do not yield a positive remainder at sqrt R.
A proof that used (9) as if its loss were
o(D_0) all the way from R^alpha to sqrt R
would be incorrect.

## 5. Near-square-root lifting to the twin witness

Take H0=4 floor(sqrt R/(log R)^B), B>0 fixed,
and H_m=ceil(4 sqrt(2R+1)). There are
O_B(loglog R) doublings. Every H_i has
log H_i comparable to log R. Thus the full
distinct loss in (9) is

    O_B(R loglog R/log^3 R).                      (10)

If D_0=omega(R loglog R/log^3 R), some endpoints
survive to H_m. For lambda=1/4 their gain is
<=H0/4<=H_m/4, and (1) of 5b148fe (terminal
idle witness) implies they are twin centers.
In fact G remains o(H_m), since H0/H_m->0.

In root-mass form, if N_s>>R and C_s/N_s=O(log^2 R)
at H0, the total root mass lost is at most

    O_B(R sqrt(loglog R/log R))=o(R),

by (8) on the disjoint removal set, because
N_s=O(R) for the canonical root family. Thus
all but o(R) of these successful roots lift
to the square-root twin witness with unchanged
endpoints and gains. More generally the
sufficient condition is
C_s/N_s=o((N_s/R) log^3 R/loglog R).
This is consistent with the semiprime frontier
criterion of d9f6049, and is a transport version
of it. It does not prove that the required
near-square-root success set exists.
No conditional independence between stages is
assumed, and no full-cohort small energy is
needed.

## 6. Executed finite audit

Source research/min_local_negative_height_doubling_rigidity_audit.mjs
commit 6e2d5693bc7d9ec0dbf880de26744c122a27eab2,
blob ed856815a78e95c29fbca88b40e8a3653badd125.
Executed in ECMAScript research runtime and fetched at that
exact commit and re-executed, with identical output.
Reproduce with node on the source. No separate Node or
Lean process invoked.

Five slabs R=12000,48000,192000,480000,1000000,
all canonical roots, first heights starting at
H0=max(64,floor(R^.24)), doubled up to
Hmax=ceil(4sqrt(2R+1)), including final partial
doubling. In these finite slabs H0 is always 64.
Stop a root when its next gain would exceed
floor(Hmax/4); earlier height records are retained.
All relevant successful first passages are counted:
a gain exceeding this global cap cannot later qualify
at any of the target heights. This is a gain-truncated
audit, not a computation of unrestricted average gain.

    canonical roots                     288671
    completed events                    5759768
    event barrier checks                5853506
      including first over-budget event
    first-height passage checks         1804540
    low-budget passage incidences        887500
    consecutive section incidences      1516380
    fixed-budget rigidity checks         194933
    low-budget dyadic rigidity checks    335414
    widened-budget rigidity checks       428638
    exact filtered support comparisons        9
    exact filtered root incidences       437564
    exact filtered surviving masses       30912
    distinct endpoint/roughness checks   135866
    failing endpoints                     25903
    stationary survivors                 109963
    distinct section recurrence checks       28

All assertions passed. The asymptotic upper-sieve
constant in (6) was not obtained from these data.
The normalized finite loss B_H log^3(H)/R was
computed for each stage, but is not used to
extrapolate the implicit constant.

Example R=1000000, canonical 166667 roots:

    H       low-gain roots  distinct endpoints  failing before next H
     64         44670            21993             5516
    128         50482            16555             3861
    256         53554            12716             3212
    512         57087             9510             2219
   1024         60017             7296              591
   2048         74771             6706                3
   4096        101320             6704                0
   5657        115938             6704                -

The increasing number of qualifying roots does
not imply an increasing number of distinct states.
For example at H=1024, 7375 distinct endpoints
qualify under the next height's widened budget
512; applying the exact stationary filter yields
6706 distinct endpoints at H=2048, precisely the
direct computation. At H=2048 the analogous
widened set has 6730 endpoints and yields 6704
at H=4096. All surviving multiplicities match.
This is the finite signature of (4)-(5).

## 7. Remaining target and research direction

The first goal, a height-doubling theorem with
a distinct-state loss estimate, is obtained.
There is a positive-density-in-the-sieve-scale
small-exponent lift, but it is not a new
near-square-root lower sieve or an unconditional
nontrivial upper bound on gain at square-root
height. The gain barrier exposes a limitation
of the originally proposed iterative mechanism:
a low-gain upper success is necessarily idle
through the last half-height interval. Simply
stacking incremental low-gain jumps cannot
generate such successes in that interval.

The next question is where the low-cost
endpoint states are created BELOW the
barrier: quantify the joint distribution
of their gain, position and next clock,
with a relaxed intermediate budget or
a restart of the gain origin. To reach
the near-square-root scale one still
needs a lower bound on that successful
population or a sharper cumulative-loss
estimate (not merely (6) with unknown
constants). No twin-infinitude proof,
Lean verification, or changes to canonical
Lean targets/sibling branches.
