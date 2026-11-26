# Negative MIN: adaptive local-moment transfer and restricted-absorption probability

2026-11-27 JST. Continuation of 8d832744ce5a0c90afc0ea2129269b21a4ef5082.
The previous local-moment theorem used a complete primorial
through O(L), hence L=O(log R). Here we replace it by a small
primorial plus adaptively pinned positive tests and a block
Bonferroni sieve for the denied tests. This extends both the
forward moment asymptotic and the near-square-root weighted
bad upper bound to L<=c_r (log R)^2/loglog R. We also derive
an exact conditional mass-transport identity and a uniform
preemption-probability bound relating the local moments to
restricted absorption at cutoff L+1. The latter isolates a
formal probability problem and admits a low-variance numerical
control. The actual near-square-root lower bound and twin
infinitude are not proved. No claim of literature priority
or Lean verification.

## 1. Set-up: local arrival at a stationary center

Use the canonical negative MIN root A in [R,2R], 6|A,
initial h=3, with height h=n+a/2. Let H be the first
POST-tick height, L the full gain budget, m_a(H,L) the
mass of successful roots ending at a. Assume
H>=35L/4+73, H+L=o(R). The missed-clock barrier
(15daec2) and local arrival characterization (8d83274)
give, away from slab boundaries,

    m_a(H,L)=1{d_3(a)>H} b_L(a),
    b_L(a)=sum_(0<=g<=L, 6|g) 1{A=a+g reaches a
                                  within T_g ticks},
    T_g=floor(9g/4+8), Z=Z_L=2 floor(9L/4+8)+7.

Every such stationary survivor is divisible by six and
rough for all odd primes <=Z. These facts use
(2H-5)/3>Z. The local arrival simulation through T_g
uses only primes <=Z, by the height-local factor rule
p|(2b+1) at even absolute tick, p|(2b-5) at odd
absolute tick, b=h+1. At that tick its eligibility
test is a mod p == -d-1 or -d+1 respectively, where
d is the remaining displacement to target a. The
least eligible prime wins. Stop on overshooting a
or reaching it, or at T_g. This description is exact
on the actual physical slab and also in the finite
formal product-coordinate model.

Let V(t)=prod_(5<=p<=t)(1-2/p).
Define mu_r(L)=E[b_L^r | Z-rough] as in 8d83274,
on the exact product space of a/2 parity and a mod p
for primes <=Z, with a mod3=0 and a mod p avoiding
+/-1 at all p>=5. For every fixed positive integer r,
mu_r(L)>=1; the previous mass-transport argument gives

    mu_1(L)<=1/V(Z)<<log^2(L+2),
    mu_r(L)<=(floor(L/6)+1)^(r-1) mu_1(L).        (1)

The local model does not by itself describe actual
endpoint statistics at near-square-root cutoffs.

## 2. Adaptive transcript for joint local arrivals

Write X=log R, l=log X. Fix the moment order r>=1.
Take a sufficiently small absolute kappa0>0 and

    z=kappa0 X,
    L<=c_r X^2/l,

with c_r chosen sufficiently small after r,kappa0.
Fix j=a/6 modulo

    M0=2 prod_(5<=p<=min(z,Z)) p.

By the Chebyshev prime-product bound choose kappa0
so M0<=R^u with u=1/100, for all sufficiently large R.
Retain only the small-residue classes consistent with
Z-roughness at primes <=z. These classes fix a/2
parity as well as the small-prime residues.

Expand b_L^r into the ordered r-tuples (g1,...,gr)
of canonical offsets, including zero and repetitions.
For each fixed tuple and fixed small-residue class,
simulate the r local arrival tests consecutively,
sharing all positive pins and denied residues on
medium primes z<p<=Z. Unqueried medium residues
are initially unrestricted except that +/-1 are
denied (target roughness). At each tick the list
of eligible-height candidate primes is known.
It has at most one medium prime for large R, since
Z=O(L+1)<z^2. All smaller factors are already fixed,
and a medium candidate which is checked and matches
must win the tick. If its residue is not known, test
one value. The positive branch pins it; the negative
branch denies it. Repeated known tests are deterministic.
Discard positive branches inconsistent with earlier
denials, or overshooting the target. A successful
leaf represents exactly a joint arrival event and
its local coordinate restrictions. Different leaves
for the same tuple and small class are disjoint.
This is not an independence assumption on the
adaptive sequence of chosen positions.

For an accepting leaf let P be the product of its
distinct medium positive pins. Let B_p be the
denied residues (including +/-1) at each unpinned
medium prime, nu(p)=|B_p|. At pinned primes all
previous denials and endpoint roughness have been
checked; no further negative test is needed there.
Discard impossible leaves. Define

    beta=prod_(z<p<=Z, p not pinned)(1-nu(p)/p).

Under the UNCONDITIONED independent uniform medium
residue law the leaf weight is beta/P.
(The conditional Z-rough law is obtained only
after summing and dividing by V(Z).)

Let T=sum_i T_gi<=r floor(9L/4+8). Every newly
pinned medium prime fires and consumes >z-1 gain
in one of the successful simulations. Thus

    #pins <=r L/(z-1)=K0,
    P<=Z^K0.                                     (2)

Each accepting transcript is determined by its
positive-query tick slots in the r simulations:
all remaining tests are deterministic or negative.
There are at most T slots (pad each simulation
by its fixed time budget if it stops early).
Hence the number of accepting leaves is at most

    sum_(k<=K0) binom(T,k) <=(T+1)^(floor(K0)+1).

For c_r sufficiently small both P and this leaf
bound are <=R^u (when no medium prime exists the
single leaf suffices). In addition there is a
useful *weighted* leaf bound,

    sum_leaves 1/P <=(1+1/z)^T <=exp(T/z).         (3)

Indeed a new medium query sends the weight of a
node to its negative branch unchanged and to its
positive branch multiplied by 1/p<=1/z.
Pruning can only reduce the weight. Pad the
tree through T slots; induction proves (3).
This is an upper bound even when denied-set
constraints are omitted from the weight, not
an approximation to their conditional probabilities.

The total medium forbidden density obeys

    lambda=sum_(unpinned medium p) nu(p)/p
            <=2 sum_(z<p<=Z)1/p + T/z
            <=C+T/z.                            (4)

The first sum is bounded uniformly since
log Z/log z<=2+o(1), by Chebyshev dyadic sums
(or Mertens). Each adaptive negative query adds
at most one forbidden value.

The following normalization is essential. For fixed
r, sum beta/P over all accepting leaves, tuples and
allowed small classes, dividing by M0. The result is
exactly

    (1/M0) sum_(j0,tuple,leaf) beta/P
                      = V(Z) mu_r(L).            (5)

It is an exact finite CRT identity, including all
joint correlations. No full primorial through Z
is needed in the actual integer count.

## 3. Medium Bonferroni and free-prime block sieve

We give the sieve polynomial explicitly; it is
sufficient to use Chebyshev and Mertens estimates
already used throughout the branch. For a prime p
with forbidden residue set B_p write I_p=1 if the
argument lies in B_p. On any finite block of
primes put I_S=prod_(p in S) I_p. For even n,

    U=sum_(|S|<=n) (-1)^|S| I_S,
    D=sum_(|S|=n+1) I_S,
    U-D <=1{no violation in block}<=U, U>=0.

These are the elementary Bonferroni inequalities.
Under independent uniform residues the expectation
of D is at most lambda^(n+1)/(n+1)!, where
lambda=sum nu(p)/p in the block.

Use one medium block of all unpinned z<p<=Z.
Choose even n0=2 floor(u X/(2 log Z)), dropping
this block if empty. The largest divisor used
including the difference polynomial is at most
Z^(n0+1)<=R^(u+o(1)). Denote the medium
expectation error by delta0. From (4), for c_r
sufficiently small one has lambda<=n0/(100e)
and T/z<=n0/100 for all sufficiently large R
in the nonempty case. Hence

    delta0<=100^(-n0-1),
    exp(T/z) delta0 <= exp(-Omega(X/l)).          (6)

For the small-L regime this is also immediate
if the medium block is empty (error zero).
The displayed constants are inessential and can
be achieved simultaneously with (2).

For a collection of free primes Z<p<=Y, disjoint
from the medium primes and with at most two
forbidden residues at each prime, partition them
into logarithmically geometric blocks:

    y_i=Y^(2^(-i)),
    block i: max(Z,y_(i+1))<p<=y_i,

stopping when y_i<=Z. On each block
lambda_i=sum nu(p)/p<=C1 uniformly: the
logarithmic endpoints differ by a factor two.
The independent survivor product V_i is
bounded below by a fixed positive constant
v_* (p>=5 and nu(p)<=2).
Take even n_i=2 ceil(s+i) for s>=1.
With U_i,D_i as above,

    sum_i E D_i / V_i
          <= v_*^(-1) sum_i C1^(n_i+1)/(n_i+1)!
          = epsilon(s) ->0 as s->infinity.

The divisor support in products of all block
polynomials, including one difference polynomial,
is at most

    exp(sum_i (n_i+1) log y_i)
                   <= exp(C2(s+1) log Y),        (7)

with absolute C2. This is why the free sieve
works even when log Y=o(log R) decreases very
slowly relative to log R. A single Bonferroni
truncation over all primes would not give this
uniformity.

Combine all blocks (medium plus free) by

    U_all=prod_i U_i,
    L_all=U_all - sum_i D_i prod_(j!=i) U_j.

The true combined survivor indicator lies
between L_all and U_all pointwise. This follows
by telescoping the difference between two
products of nonnegative factors and replacing
all other factors by their upper bounds.
No lower polynomial is required to be
nonnegative. On expansion, the coefficient
of every squarefree divisor is 0,+1 or -1:
the upper term uses at most n_i primes from
each block, and a difference term uses exactly
n_i+1 in one designated block, at most n_j
in the others. These support patterns are
disjoint. In particular the absolute
coefficient bound does not grow with the
number of blocks.

Under the independent residue law, put
V_f=prod_(free p)(1-nu(p)/p). The two
combined expectations differ from beta V_f
by at most

    O(V_f [delta0 + beta epsilon(s)])

when epsilon(s)<=1, by the per-block product
bounds (and absorption of delta0 epsilon(s)
in the delta0 term). For a fixed sufficiently
large s this also supplies constant-factor
bounds on the beta term, with the stated
additive medium error.

## 4. Count in an actual progression

Fix j0 mod M0 and an accepting transcript.
The pinned positives select one progression
modulo M0 P in j, by CRT. For the bad-center
count we additionally impose a+e=q r0, with
q the smaller prime factor of a composite
neighbor, and e=+/-1. We use r0 for the
semiprime cofactor, not the moment order r.
At near-square-root height the endpoint is
K-rough with K comparable to sqrt R/log^B R.
Thus q>K, q<=sqrt(2R+1), and q is coprime
to 6 M0 P. Imposing q|a+e further selects
one progression modulo q M0 P in j.
The count may ignore the condition that the
cofactor is prime; free-prime roughness is
a necessary condition and is sufficient
for this upper-bound argument. In the
progression parameter the two endpoint
forms have two distinct forbidden residues
at each odd free prime p not dividing the
progression modulus. Choose Y<q in the
bad count. There is no such additional
modulus in the full-success count.

For a squarefree divisor d of the unpinned
medium and free primes, the CRT remainder
for its violation indicator I_S in the
progression is at most prod_(p|d) nu(p)<=d.
If the combined polynomial support is <=D_*,
its total absolute error is <=sum_(d<=D_*) d
=O(D_*^2). Use the actual real progression
length as main term, with no need to round
each individual divisor's main term separately.

Choose Y and s with
C2(s+1) log Y<=u X. Then by (7) and the
medium bound D_*<=R^(2u+o(1)).
The number of progression/transcript terms
summed, including the O(L^r) tuples and all
small classes, is at most R^(2u+o(1))
without the q factor. With q and e it is at
most R^(1/2+2u+o(1)).
Therefore all CRT errors are bounded by
R^(1/2+6u+o(1)) even for the bad count,
and much less without q. This is negligible
against the main log-scale estimates below.
Pin modulus P does not enter this CRT
remainder, since only coprime unpinned
primes are expanded.

When summing the medium main-term errors,
the progression length contributes 1/P.
By (3),(6), for each tuple and small
class the sum delta0/P is at most
exp(-Omega(X/l)). The O(L^r) tuple count
and averaging over M0 cannot undo this
saving. It is o(V(Z) mu_r(L)), uniformly:
mu_r>=1 and V(Z)>>1/log^2(Z+2).
This weighted error estimate is important;
bounding the medium error by the raw
number of transcripts would not suffice
at the full L=c_r X^2/l scale.
Thus (5) determines the main weighted
coefficient after summing all leaves.

For forward equality restrict endpoints
initially to [R,2R-L] so all offsets
remain in the original root slab. The
omitted endpoint boundary contributes
O((L+1)^(r+1)), negligible here. For upper
bounds use the entire enlarged endpoint
interval [R-L,2R], ignoring the birth
boundary if necessary. Its length is
R+O(L) and the same argument applies.

## 5. Extended forward local-moment asymptotic

Let H->infinity, log H=o(log R),
H>=35L/4+73, and use

    0<=L<=c_r (log R)^2/loglog R.                (8)

For the exact stationary survivor d_3(a)>H
the forbidden classes at a free prime p>Z
are determined by the fixed a/2 parity
and the short/long clock representatives
in 15daec2. All p<= (2H-5)/3 forbid both
neighbor residues, and no p>2H+1 is
relevant. Thus for Y=2H+1

    V_f=(1+O(1/log H)) V(H)/V(Z),

uniformly in all small classes and pins.
The possible variation is confined to a
constant-ratio prime band; Chebyshev
gives its reciprocal sum O(1/log H).
Choose s=s(R)->infinity slowly enough
that C2(s+1)log Y<=u log R.
This is possible throughout log H=o(log R).
Then epsilon(s)=o(1).
Sum the upper and lower polynomial counts
using (5) and section 4. It follows that

    sum_a m_a(H,L)^r
           ~ (R/6) V(H) mu_r(L),                (9)

uniformly for (8) and the stated heights,
for every fixed r. In particular (9)
includes the exact forward mass and
energy formulas (r=1,2) from 8d83274
with a gain budget larger by order
log R/loglog R. At sufficiently small
fixed polynomial height H=R^alpha, use a
large fixed s and take alpha sufficiently
small; this gives two-sided constant-factor
bounds rather than relative asymptotics.
The argument supplies no lower formula
for H near sqrt R.

## 6. Extended near-square-root weighted upper sieve

Let B>0 be fixed and
H=4 floor(sqrt R/log^B R). With (8) the
local profile conditions hold for all
large R. For an endpoint count choose a
fixed sufficiently large s, and Y=R^xi,
xi>0 small enough that (7)'s budget
holds. Then Y is below K and q, and
Z=polylog R<Y. Use both forbidden
neighbor residues at every free prime
Z<p<=Y. Mertens gives

    V_f=V(Y)/V(Z) << 1/[V(Z) log^2 R].

For the bad count fix a side and a prime
q in (K,sqrt(2R+1)]. The other neighbor
is rough, and any composite neighbor is
a semiprime for sufficiently large R
(K^3>2R+1). The preceding CRT argument
applies with the additional q progression.
The main weight (5) cancels V(Z).
Sum q using the reciprocal bound
O_B(loglog R/log R) from d9f6049.
All error terms are negligible as
shown in section 4. Therefore, uniformly
for (8),

    sum_a m_a(H,L)^r << R mu_r(L)/log^2 R,
    sum_(bad a) m_a(H,L)^r
          <<_B R loglog R/log^3 R * mu_r(L).      (10)

These are all-event-depth estimates.
The upper bounds do not require an
asymptotic for actual twins or for the
formal moment coefficients as L grows.
For example by (1) with r=1,2,

    N_bad(H,L) << R (loglog R)^3/log^3 R,
    C_bad(H,L) << R (loglog R)^2/log R,

at L<=c (log R)^2/loglog R (choose c for both
moment orders). The second uses
mu_2(L)<< (L+1) log^2(L+2).
The corresponding total-success mass
is O(R (loglog R)^2/log^2 R)=o(R).

As in 8d83274, a forward lower bound
N_success(H,L)>>R mu_1(L)/log^2 R
on unbounded slabs would imply twin
infinitude from (10). In this local
budget regime the lower bound is still
a weighted stationary-rough-center
lower sieve near sqrt R. The expanded
budget does not remove that remaining
obstruction, nor does it establish
N_success>>R or the bad-energy bound
for the full L=H/4 budget.

## 7. Exact restriction/preemption identity for formal moments

This section is independent of actual finite-slab
sieve transfer. Let L>=6 be integer and choose
a cutoff y>=L+1, with P_y all odd primes <=y.
It is enough to take y=L+1. At a formal target
a condition all residues up to Z_L to be rough.
For a root a+g with 6|g, 0<=g<=L, run the
restricted P_y process to absorption. All
restricted absorption paths exist in the
formal finite-alphabet model by the spatial
wall theorem. Denote by b_(y,L)(a) the number
of these roots absorbed exactly at a with
gain<=L. The low endpoint coordinates are
uniform conditional on y-roughness (if
y>Z_L one can condition also on these extra
irrelevant coordinates; for the statements
below take y<=Z_L). Define

    nu_r(y,L)=E[b_(y,L)^r | y-rough].

The full local hit at a of any root within
gain budget L uses only labels p<=L+1<=y,
so it follows the restricted trajectory.
Because a is rough for P_y, it is also a
restricted absorber. Conversely a restricted
ancestor which has no omitted prime preempting
a restricted firing before arrival is a full
local ancestor. An omitted label q>y can
never win a tie with a restricted p<=y;
if it preempts, its gain q-1>L overshoots
the target immediately. This gives an
exact equivalence for a specified restricted
ancestor, not just a sufficient condition.

For any such restricted path its elapsed
completed waits W<=T_g by the mod-30
potential (which holds for restricted
rules containing 3 and 5). Its preheights
and all possible omitted clocks up to
arrival use primes <=Z_L. At each tick
strictly BEFORE the next restricted
firing, inspect the height factor list;
an omitted q>y can preempt only if its
target-coordinate residue equals
-d-1 or -d+1, where d>0 is the current
remaining displacement. For each q
collect the DISTINCT residues of these
tests, excluding +/-1, into B_q.
This list is determined by the restricted
path and its low coordinates, not by
the omitted coordinates. Conditional on
the target being rough for all p<=Z_L,
the omitted coordinates are independent
uniform over p-2 allowed residues.
The probability of no preemption is

    Pi=prod_(y<q<=Z_L)(1-|B_q|/(q-2)).          (11)

For simultaneous survival of r restricted
ancestors, take the union of their B_q
at each q. This retains the correlations
rather than multiplying the r individual
probabilities. Formula (11) with this
union is exact for the joint hit.

There is a uniform lower bound. All source
offsets are positive even d<=L. Thus for
any q, even for the union over arbitrarily
many paths,

    |B_q| <= floor(L/2)+1.

Indeed all tests are among odd integers
-L-1,...,-1 (or the corresponding list
when L is odd), reduced mod q.
Since q>y>=L+1, q-2>=L, so each fraction
is <=1/2+1/L<=2/3. Each tick can test
at most one omitted prime: (L+2)^2>Z_L
for L>=6. Hence for r paths

    sum_q |B_q|/(q-2) <= r T_L/L
                             <= r(9/4+8/L).

Using -log(1-t)<=3t for 0<=t<=2/3,
we obtain Pi>=exp(-11r). More sharply,
on [0,1/2+1/L] the ratio -log(1-t)/t is
at most 2 log 2+o(1), so uniformly as
L->infinity,

    Pi >= exp(-(9r/2) log 2 - o(1)).

Sum this exact joint survival law over all
ordered restricted ancestor tuples, then
the low residue classes. It proves

    exp(-11r) nu_r(y,L) <= mu_r(L) <= nu_r(y,L),
    mu_r(L) >= (2^(-9r/2)-o(1)) nu_r(y,L).        (12)

The upper inclusion holds because actual
successful paths cannot use omitted
labels within budget. These comparison
constants do not require any control
on restricted event depth or number
of tested omitted prime coordinates.
For smaller y<L+1, (11) remains a
sufficient matching-path probability;
the two-sided comparison (12) need
not hold. Adding allowed primes can
both remove and add ancestors, so
naive cutoff monotonicity is false.

## 8. Root-biased mass transport and a concrete formal target

For y=L+1 let A=6j be uniform over its
restricted canonical period M_y=2 prod_(5<=p<=y)p.
Let G_y(A) be the full gain to the restricted
absorber a_y(A). Its distribution is the
unconditioned small-prime root distribution.
By periodic translation, each canonical
root contributes once to its absorber,
which is one of M_y V(y) rough classes.
The same counting as in (10) of 8d83274,
now restricting gain, gives

    nu_1(y,L)=Pr_root(G_y<=L)/V(y).

For every root with G_y<=L compute Pi_y(A)
from (11) for its path, relative to its
own absorber (and condition the independent
omitted coordinates at that absorber).
Translation of the root by the small
period preserves all low path data.
Summing over the roots rather than targets
therefore yields the exact identity

    mu_1(L)= 1/V(L+1) *
               E_root[1{G_(L+1)<=L} Pi_(L+1)].   (13)

More generally for y<L+1 the right side
(with V(y)) equals the contribution of
those full local hits using only labels
<=y, since their restricted path must
match until arrival. Here (11) supplies
the matching event even if an omitted
preemption could lead to a different
full trajectory. The equality (13)
uses y=L+1, where all local hits are
of this restricted form.

Combining (12)-(13) and Mertens,

    mu_1(L) is comparable, uniformly, to
           (log L)^2 Pr_root(G_(L+1)<=L).        (14)

Thus a positive absolute lower bound
on the fraction of roots absorbed by
the restricted alphabet <=L+1 within
gain L would imply mu_1(L) >> log^2 L,
matching (1) in order. The formal
unboundedness problem is also isolated:
mu_1(L)->infinity iff the quantity
on the right of (14) tends to infinity.
No such restricted fraction lower
bound beyond the trivial static-rough
probability is proved here.

If G_y is much smaller than y, the
preemption loss is even absent:
the event gain barrier 676c259 gives
b<=35(G_y+10)/18 for every completed
preheight on the restricted path
(the proof applies to this restricted
rule containing 3,5). If this is below
(y-1)/2 then no omitted q>y can be a
height factor before arrival, and Pi=1.
This includes G_y<=y/4-O(1) for
large y. Also directly the number of
pre-arrival tests at heights >=(y-1)/2,
divided by y-1, bounds 1-Pi by the
union bound. These reductions explain
why (13) can be estimated without
sampling the very uneven conditional
endpoint basin masses. They are
not a proof of the limiting probability.

Even a proof of mu_1(L)~const log^2 L
in the formal product model would not
alone transfer (9) to H near sqrt R.
A full proof still needs a lower
bound on actual successful root
mass at that height, or a new
dynamical witness with larger gain
budget that avoids the static
stationary-sieve reduction.

## 9. Executed reproducible audits

All three scripts below were executed in the
ECMAScript research runtime, fetched at the
exact remote commit, and independently re-run
with identical output. Reproduce with node.
No separate Node or Lean invocation.

A. research/min_local_negative_adaptive_profile_block_sieve_audit.mjs
   commit f415197a946583849d41b629ed0093893c1d6a99
   blob 3e30abea31af24e41e2721f9c5ee0ac67dc0231d

Enumerate five complete small-prime periods
with (L,cut)=(6,7),(12,7),(18,11),(24,11),(24,13).
For every allowed small class and ordered offset
tuple of length one or two, compute accepting
leaves with positive pins and denied sets.
Use integer counts of medium assignments and
compare to the previously computed exact
rational moments in 8d83274. The two different
cuts for L=24 give identical moments.
Check pin-gain cap, reciprocal-pin weight
bound, and one medium factor per tick.

    small classes                       3570
    ordered tuple controls            103140
    decision tree nodes              5579243
    query branches                   1820575
    accepting leaves                  174816
    pin budget checks                 174816
    reciprocal leaf weight checks     103140
    one-medium-factor checks         5215111
    exact integer moment comparisons      10

Independent block polynomial controls:
120 abstract blocks of forbidden tests with
40320 pointwise comparisons and 40320
coefficient checks, 120 expectation checks.
80 finite arithmetic progressions (with
separate fixed moduli), 5120 divisor
CRT remainder checks. All upper and
lower polynomial inequalities passed.
These tests verify the algebra and
remainder mechanism, not a numerical
asymptotic sieve constant.

Actual physical slab controls:
R=12000,48000,192000,1000000,
L=24,48,96, sampled stationary survivors,
16399 local reach comparisons against
independent ordinary next-event calculation,
6534 valid medium pins. The small finite
test cutoffs were chosen to ensure the
one-medium-factor property; they are
not the asymptotic z=kappa0 log R
parameter regime. All assertions passed.

B. research/min_local_negative_large_local_profile_sampling_audit.mjs
   commit 295c8f521d32d09d254f9f92ebe90dd88f51b367
   blob c3635c3518aecb59766b1a49011a89446aa518e9

Efficient event-driven conditional endpoint
profiles. For each sampled product environment
generate the eligible-label lists for all
even source offsets d in [0,L], using the
residue tests for p<=Z_L. Compute each clock
in relative absolute time n+a/2, where a is
the target. Cache the final outcome keyed
by (source offset, firing time). Shared keys
have identical futures. The simulation with
all primes <=Z_L is exact for the local hit
at displacement <=L: a hit must occur by
T_g; no omitted larger prime can affect
the ticks before such a hit, and the
restricted potential also bounds the time
of any restricted hit. The same argument
checks the independent tick replay for
smaller cutoffs.

432 fixed-seed pseudorandom environments:
256 at Lmax=6144, 128 at 24576, 48 at 98304.
30067355 event-call evaluations, 22207527
new cached event keys, 6035323 memo hits,
44898 arrival-time checks; 4680 independent
tick comparisons (both full and restricted),
1728 paired cutoff comparisons. An initial
scratch comparison failed because its
smallest-factor sieve overwrote earlier
factors, so the reference tick chose the
wrong prime at a simultaneous clock.
The inner sieve was corrected to preserve
the least factor; all final comparisons pass.

Conditional endpoint sample means at the
largest budget in each group:

    L        samples    mean b_L    mean b_L^2
     6144       256       28.21875    2642.140625
    24576       128       39.35156    6621.304688
    98304        48       50.20833   13879.625

These are sample means, not exact rational
moments. The last group has high variance
(maximum b_L=640). Paired restricted
cutoff comparisons observed 512 instances
of a root present in the restricted profile
but lost in the full profile, and 26809
instances gained. Counts are overlapping
across different cutoffs. Hence inclusion
for arbitrary smaller cutoffs is not valid.
For y=L+1 the full profile is necessarily
a subset, in accord with (12).

C. research/min_local_negative_root_absorption_preemption_audit.mjs
   commit 859420c95f8a8e4ba0aff2f667ba6a69f3c2789e
   blob b90d21835ae3fd2e0cabbbadeec8c3e0778d1985

Sample uniform canonical ROOT residues for
the restricted alphabet <=L+1 (not
conditioned rough endpoint coordinates).
Run to absorption or gain-budget stop.
For each success record the complete path
and compute the exact no-preemption
probability (11) as a product over
distinct forbidden residues. The product
is numerically evaluated; its formula
is exact. Independently sample omitted
target coordinates conditioned rough,
shift them by the restricted final gain
to obtain the root coordinates, and
replay the full local tick rule. Check
that the restricted root reaches that
same absorber iff no forbidden test
matches (omitted prime would overshoot).
11008 environments, 7790 restricted
budget successes, 3218 gain stops,
178540 completed events, 7974313
pre-firing tick/omitted-factor checks,
98613 distinct forbidden-set checks,
7790 uniform hazard-bound checks,
7790 exact matching-event comparisons.
All assertions passed. Joint moment
comparison (12) follows from union
of the forbidden sets; this audit
does not implement a separate joint
hazard test (jointHazardChecks=0).
The finite joint adaptive-moment
controls are in audit A.

    L       samples    restricted success   Pi conditional   mu_1 estimate by (13)
    96        4096          .60498             .990569            5.21602
    384       3072          .69206             .996035            9.93806
    1536      2048          .78613             .996578           16.99273
    6144      1024          .85449             .996797           26.02883
    24576      512          .91016             .997584           37.21854
    98304      256          .91797             .996352           48.42468

At the largest L the exact reciprocal
rough density is 52.945158..., so the
weighted restricted fraction in (13)
is .9146196. At that L 168 of 256
roots are absorbed within L/4, and
127 within L/16. These are finite
fixed-seed sample proportions, not
asymptotic probability lower bounds.
The root-biased estimator in (13)
uses bounded weights before multiplying
by 1/V(y), avoiding the high variance
of endpoint basin counts; different
sample means in B and C need not agree
exactly. No claim that F_y(y) tends
to one is made.

## 10. Research status

The adaptive residue transfer extends
the exact forward moment formula to
larger local gain budgets (8), without
assuming independent adaptive histories,
and gives the corresponding all-depth
weighted bad upper sieve near sqrt R.
The block sieve uses only explicit
Bonferroni polynomials and CRT remainder
bounds; no new near-square-root lower
sieve theorem is assumed. The exact
absorption/preemption law (13) and
comparison (12) supply a concrete
formal problem for the growth of mu_1
and higher moments, together with
a more efficient numerical estimator.

The formal restricted absorption
probability still needs a nontrivial
analytic lower bound. More importantly
the lower estimate (9) still requires
log H=o(log R) (or small fixed polynomial
H for constant factors), rather than
H~sqrt R/log^B R. A proof of twin
infinitude must overcome this actual
finite-slab lower-bound gap or use a
different genuinely large-gain dynamical
route. Neither that proof nor the
full-budget bad energy estimate or
Lean formalization is obtained here.
No canonical Lean target/sibling
branch changes.
