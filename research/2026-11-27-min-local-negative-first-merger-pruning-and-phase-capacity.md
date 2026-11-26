# Negative MIN: first-merger cuts, sparse high-label collisions, and low-run phase capacity

2026-11-27 JST. Continuation of 939e39d9e0a1e55a43f7396b33714f81e59a4054.
Work toward the actual fixed-time mean-gain contradiction, rather than
a formal-to-actual square-root lower sieve. We identify a failure of
the proposed nested gain-threshold energy recursion, replace it by an
exact threshold-overlap identity and a physical first-merger ledger,
and restrict the large-slow supply bound to pairs that share a future
large-slow event. Same-tick and short-lag high/high collisions have
additional arithmetic rigidity. Long-idle mergers admit a four-form
upper sieve. For the small-label side, an exact periodic phase-average
capacity replaces a worst-case spatial wall in light-prefix estimates.
These are paper-level deductions and reproducible finite calculations,
not Lean verification, literature priority claims, or a proof of twin
infinitude. In particular the remaining long-history small-label
mergers and heavy cohorts are not controlled.

## 1. Domain and first-merger ledger

Actual canonical roots A in [R,2R], 6|A, start at position a=A,
absolute tick n_A=3-A/2, height h=n+a/2=3. Each root has elapsed
horizon T=ceil(8 sqrt(2R+1)), is included at its birth tick and
through its retirement tick n_A+T, then is removed. Gain is A-a.
All states have a in [R-2T-6,2R], h in [0,T+3], and n<0 for
sufficiently large R. At a firing of label p the gain increment
g=p-1 is positive; the wait w since that root's last arrival or
birth can differ between roots sharing the same firing key.
The event winner is the least (wait,p); at a fixed tick this
is the least eligible p. A slow incidence has 4w>=p.

At a target (b,n), let i be the number of roots that occupy b
both immediately before and immediately after this tick, m_p
the number jumping there at this tick from b+p-1, and beta
the number of births at this state (0 or 1). Retirements are
processed after the tick. The incoming jumping branches for
different p have distinct predecessor positions; all roots
within one such branch were already together before the tick.
Exactly the following number of unordered pairs first merge:

    Delta P(b,n) = beta (i+sum_p m_p)
                    + i sum_p m_p
                    + sum_(p<r) m_p m_r.                       (1)

Indeed deterministic shared absolute-time futures cannot
separate before either root retires. A pair from distinct
incoming branches has not previously merged while both active.
A birth is new by definition. Therefore summing (1) gives
the number P of unordered distinct root pairs sharing any
physical state during their overlapping active intervals.
The same count is obtained by removing, at every retirement,
the pairs between the retiring root and the other roots in
its then-current state. Every previously merged pair is
removed exactly once, at the earlier retirement. This is
an exact physical merger ledger, not the energy of the
elapsed-time endpoint distribution; retirement ticks differ.

In particular a proposal to treat gain-threshold partitions as
nested is invalid. Although a physical merger is permanent
while both roots are active, roots with different A have
different gains at the same position. They can share the
first crossing of J but have different first crossing keys
of 2J, even when both crossings occur before retirement.
The audit gives A=3048,3054, J=6, same first crossing
(a,n)=(3048,-1505), but first crossing of 12 at
(3036,-1493) and (3048,-1505), respectively.
A recurrence justified only by nesting of these partitions
therefore cannot be used. This does not disprove a numerical
upper inequality with separately established hypotheses.

## 2. Exact threshold-overlap and a gain-local key bound

For a completed physical firing e=(a,n) of label p,
let U_e be its participating roots and g_e=p-1.
For each A in U_e write d_A=A-a for its gain BEFORE e.
Its first crossing of the integer threshold J (gain >J)
is e precisely when

    d_A <= J < d_A+g_e.

Thus for m_e(J)=number of such roots (or restrict to any
specified subset of incidences, e.g. the slow ones),

    sum_J m_e(J) = g_e |U_e|,
    sum_J m_e(J)^2 =
         sum_(A,B in U_e) (g_e-|A-B|)_+.                       (2)

Sum J over nonnegative integers; the support is below
2T+6. The second formula is the length of intersection
of the two integer threshold intervals. It is exact even
if the same two roots share many events. Finite-window
versions clip each of the intervals before intersecting.
In particular a shared crossing at a given J cannot
include two roots separated by >=g_e. This is why
gain-crossing energies and full physical energies differ.

For a prime band [Y,2Y), Y>=5, choose grid spacing
s=floor(Y/2). Assign each participating root at e to
J=s ceil(d_A/s); this grid threshold belongs to its
crossing interval. There are O(1+T/Y) distinct grid
thresholds, since all pre-gains lie in [0,2T+6].
Cauchy gives

    sum_(band keys) |U_e|^2
       << (1+T/Y) sum_(grid J) sum_(band e) m_e(J)^2.          (3)

Here m_e(J) counts all eligible crossings, so includes
the assigned subset. No assumption of monotonicity in
J is made. For a slow incidence the available credit
c_(A,e)=(4w_(A,e)-g_e)_+ is <=11g_e. The exact first
formula (2) gives the following alternative supply ledger:

    C_Y=sum_(e in band,A slow) c_(A,e)
        <=11 sum_J F_Y(J),
    F_Y(J)=sum_(e in band) m_e^slow(J).                         (4)

The number K_Y(J) of possible keys with at least one slow
first crossing at threshold J is gain-local, not simply
bounded by the whole horizon. For fixed epsilon>0 and
R^epsilon<=Y<=2T+7,

    K_Y(J) <<_epsilon
         R (1+min(T,J)/Y) / log^3 R.                           (5)

Proof: slow w>=p/4 and w<=2q(a), where q(a) is the
least neighbor prime, imply q(a)>=p/8. For fixed p
and side the spatial pin p|a+/-1 and p/8-roughness
give O_epsilon(R/(p log^2 R)) possible source positions
by the standard two-form upper sieve on the cofactor
progression, as in 939e39d. Independently the post-gain
at a first crossing is <=J+2Y, so the postheight is
<=min(T+3,11+7(J+2Y)/4), using the mod-30 potential.
At a fixed a the p-clock is spaced by 2p ticks.
Thus there are O(1+min(T,J)/Y) possible clock ticks.
Sum the reciprocal prime bound over the band.
This includes the fixed small-gain case without
assuming stationary synchronization.

Writing E_Y^slow(J)=sum_e m_e^slow(J)^2 gives

    F_Y(J) <= sqrt(K_Y(J) E_Y^slow(J)).

Equations (3)-(5) allow a scale-by-scale supply bound
from the first-crossing energy, but require bounds
on those energies at the actual large thresholds.
For top bands Y comparable to T the grid (3) has only
O(1) thresholds; they need not be the dyadic sequence
J,2J,4J,... proposed earlier. These identities do not
provide an autonomous energy recursion.

## 3. Prune the merger ledger by the common future

Let I be a set of large primes, and let S_e be the
subset of roots with a slow incidence at completed
key e of label in I. Put s_e=|S_e|, g_e=p_e-1.
Define P_I to count only unordered pairs of distinct
roots which share at least one such key with BOTH
incidences slow, during their active time windows.
In terms of (1), each pair counted by P_I has exactly
one first merger; retain that pair at its first
merger only if its subsequent common trajectory
includes such a key. The credit of the first common
event can differ because waits are arrival-dependent.
This definition keeps the exact incidence-specific
condition, not just a label or a common terminal basin.

There is an exact gain-weighted energy identity

    M_I=sum_(e in I) g_e s_e^2
       =sum_e g_e s_e
          +2 sum_(pairs counted in P_I)
                     sum_(their shared slow e in I) g_e.      (6)

Each inner sum, and each individual root's diagonal
gain sum, is at most 2T+6. Hence

    M_I <=(2T+6)(N_R+2P_I), N_R=|A_R|.                        (7)

Let A_I=sum_(e in I, s_e>0) g_e be the unweighted
physical supply capacity. The actual slow credit
of the cohort satisfies

    C_I <=11 sum_e g_e s_e <=11 sqrt(A_I M_I).                (8)

The same two-form upper sieve used in (5), now with
the full height range T+3, gives A_[Y,2Y) << RT/log^3 R
for R^epsilon<=Y<=2T+7. Summing dyadic bands gives
A_[R^epsilon,infty) <<_epsilon RT/log^2 R.
Thus the following are sufficient, actual-integer
conditions for the indicated mean credit to be o(T):

    top constant-ratio band: P_I=o(R log^3 R);
    all primes >=R^epsilon: P_I=o(R log^2 R).                 (9)

Unlike bounding the full merger energy, these
conditions do not count pairs whose common future
never has a slow high event. For J>=0, pairs with
|A-B|<=J number at most N_R floor(J/6); this bound
does not use any dynamics. Choose J=o(log^2 R),
for example the previous polylogarithmic first
crossing budget. These close pairs are negligible
in either target in (9). Only far pairs, pruned by
their common future, require the missing estimate.
Do not identify small separation with small gain
of one of the roots at its first merger.

This is a reformulation of the weighted key energy
target with a precise first-merger interpretation,
not a proof of (9). In the finite experiment below
the top-prime cutoff is T/16, not R^epsilon for all
epsilon. The largest observed pruned population is
about one fifth of the entire first-merger ledger.

## 4. Arithmetic rigidity of simultaneous jumping branches

At a physical arrival (b,n), put h=n+b/2. The inverse
jump from b+p-1 has necessary divisibilities

    n even:  p|b,   p|h;
    n odd:   p|b-2, p|h-3.                                  (10)

Indeed in the first case p|n and p|(b+p-1)+1;
in the second p|(n-2) and p|(b+p-1)-1.
Odd p permits dividing b by 2 modulo p.
In particular if distinct primes p,r arrive in
the same tick then both have the same side, and

    pr | b-c,    pr | h-c_h,

where (c,c_h)=(0,0) at an even tick and (2,3)
at an odd tick. If pr>T+3 the second congruence
forces h=c_h. Thus two incoming large labels
p,r>sqrt(T+3) can only merge simultaneously at
these reset heights. The conclusion does not
require either arrival to be slow.

There is also exact idle rigidity at these heights.
At h=0 no idle branch exists: a root occupying b
at the previous tick would have negative height.
No birth occurs there either. For an odd-tick
plus reset h=3, any idle occupant arrived at b
at h=0 (and at an even tick) and has waited the
three intervening ticks. In fact birth height is
3 and the only possible arrival height below 3
by (10) is 0 (p>=3); n at h=0 is even because
the plus-reset tick is odd. This distinguishes
the short staggered cross-side reset from a
same-tick reset collision. Small labels can
still bring arbitrarily much inherited root mass.

## 5. Upper sieve for two large simultaneous arrivals

Fix epsilon>0 and prime bands p in [Y,2Y),
r in [Z,2Z), with Y,Z>=R^epsilon and
Y,Z<=2T+7. Count triples (b,n,p,r) with
p!=r (equivalently count the key and ordered
two arrival labels; four coordinates).
The side is fixed by n. If such a pair exists,
b=c+pr k, k>=1, k<<R/(YZ).
Let delta=-2 at a minus arrival and +2 at a plus
arrival. The two source-neighbor pairs are

    p(kr+1),   p(kr+1)+delta,
    r(kp+1),   r(kp+1)+delta.                                (11)

If the p branch has a slow incidence, both
of its neighbors are p/8-rough. Fix k,p and
sift r in [Z,2Z) on three linear forms

    r,   kr+1,   p(kr+1)+delta.

All must avoid primes <=R^xi for a sufficiently
small fixed xi>0, chosen below the roughness
cutoff and the available polynomial interval
length. The forms have distinct rational zeros:
their pair determinants are nonzero. Exclude
the prime factors of their leading coefficients
and pair determinants, and the finitely many
small primes <=2 times the dimension. Their
nonzero product is R^O(1). For each remaining
prime there are exactly three forbidden residues.
The fixed-dimension upper sieve gives uniformly
O_epsilon(Z (loglog R)^3/log^3 R) possibilities.
The loss (loglog R)^3 follows by splitting prime
divisors of the excluded product at log R:
the inverse sieve factors below that threshold
cost this power by Mertens, those above cost
O(1). Use level sqrt Z; the squarefree CRT
remainder <=3^omega(d) is negligible with xi
small. This is the same sieve mechanism used
in bf8a5da. Sum k and the O(Y/log R) primes p.
For each triple of spatial data the height
congruence in (10) gives O(1+T/(YZ)) choices.
Consequently one-slow simultaneous high/high
key pairs number

    <<_epsilon R (1+T/(YZ)) (loglog R)^3/log^4 R.              (12)

If both incoming branches have slow incidences,
also sift p and kp+1 for fixed k (dimension two)
and add the fourth form (kp+1)r+delta to the
r sieve for fixed k,p. Its zeros are distinct
from the other three. For example its determinant
with p(kr+1)+delta is
pk delta-(kp+1)(p+delta)=-kp^2-p-delta !=0.
The other determinants are nonzero since k>=1,
p>=5 and delta=+/-2; exclude all their prime
divisors as above. Sift p and kp+1 up to a small
power below both cutoffs, obtaining
O(Y (loglog R)^2/log^2 R) possibilities.
The four-form r sieve costs
O(Z (loglog R)^4/log^4 R).
Multiplication and sum over k give

    <<_epsilon R (1+T/(YZ)) (loglog R)^6/log^6 R.              (13)

Dropping parity and the actual priority test only
increases these upper counts. The counts concern
distinct physical key/label pairs, not root
incidences. For Y,Z comparable to T the height
factor is O(1); all simultaneous pairs are reset
pairs for large R. For example if each incoming
slow mass is <=(log R)^3, (13) bounds the
corresponding double-slow first-merger pair
contribution in top bands by O(R (loglog R)^6),
which is o(R log^2 R). Such a mass cap is an
additional restriction, not a conclusion of
the sparse-key estimate.

## 6. Long-idle mergers with a large slow arrival

Now count a slow incoming p in [Y,2Y) at (b,n)
which merges with a root that has been at b for
age at least K at this tick. The other root can
have been born at b or arrived there earlier.
It has not fired during its current wait.
Since any eligible neighbor prime q at b has
a next clock within 2q ticks, q(b)>=(K/2)
(in fact >age/2 for the completed idle tick).
The source a=b+p-1 of the incoming root is
already p/8-rough. Fix p, side, b=pk+c;
c and delta are as above. Simultaneously sift

    k+1,   p(k+1)+delta,   pk+c-1,   pk+c+1.                  (14)

All four forms are rough to min(p/8,K/2).
Their rational zeros are distinct for p>=5:
among the three forms with coefficient p
the constants are distinct, and the root
of k+1 is not a zero of the others.
Choose K=R^kappa, fixed 0<kappa<1/2,
and R^epsilon<=Y<=2T+7. The cofactor
interval has length O(R/p) and is polynomial.
The same four-dimensional upper sieve
and exceptional product argument yield
O(R (loglog R)^4/(p log^4 R)) positions.
There are O(1+T/p) allowed arrival ticks.
After summing over p the number of incoming
physical keys with any such long idle branch is

    <<_(epsilon,kappa)
         R (1+T/Y) (loglog R)^4/log^5 R.                       (15)

For top bands, if the slow incoming mass
and the total long-idle mass at a key are
each <=log^3 R, their product times this
key bound is O(R log R (loglog R)^4)
=o(R log^2 R). This includes all arrival
histories of the long-idle branch; no depth
restriction was used. It does not prove the
mass cap or bound the short-idle branch.

## 7. Short-lag high/high arrivals and the staggered exception

Suppose now an incoming p and an earlier
arrival r at the SAME destination b have
labels in fixed constant-ratio top bands
(p,r comparable to T). Their ticks are
n,n'<n and lag delta_t=n-n'<K, with K=R^kappa,
0<kappa<1/2. If r=p and the sides agree,
the p clock difference is a multiple of 2p,
impossible. If the sides differ, p divides
both b and b-2, also impossible. Hence p!=r.
By (10) the two arrival heights are
h=c_1+i p and h'=c_2+j r, c_1,c_2 in {0,3},
with nonnegative integers i,j bounded by
constants (p,r>3). Their difference is
delta_t. Thus

    |i p-j r| <= K+3.                                         (16)

For sufficiently large R, one of i,j cannot
vanish without the other also vanishing.
If both vanish, n is a plus reset at h=3
and n' a minus reset at h=0, lag exactly 3.
This is the only staggered reset exception.
Otherwise i,j>=1. Fix p,i,j and the two sides;
there are O(K+1) integer candidates r from
(16). Distinct p,r impose one CRT class on
b modulo pr, regardless of the sides; since
pr comparable to R there are O(1) spatial
candidates. Heights determine both ticks.
By Chebyshev's prime count the total
nonreset short-lag key/label pairs number

    O(T(K+1)/log T).                                          (17)

This is o(R/log^A R) for every fixed A.
It does not require roughness or a slow
condition. With branch masses <=log^3 R,
its root-pair contribution is o(R).
If the incoming p is slow, the staggered
exception has O(R/log^3 R) possible p
keys by the two-form source sieve, and
O(1) possible earlier top r divisors of
b (since b=O(R)); the earlier tick is
fixed. Thus its count is O(R/log^3 R),
without an extra independent log factor.
With branch masses <=log^2 R this gives
O(R log R)=o(R log^2 R). No stronger
cross-side shifted-product sieve is
claimed here. In particular (13) must
not be applied to the staggered case.

A simple complementary bound removes
low-history partners of incoming top
events without ANY mass cap. For each
incoming root at a top event at (b,n),
there are at most floor(J/6)+1 possible
other roots with POST-gain <=J at this
same state, since A is in [b,b+J].
Each root has O(1) top-label incidences
through its horizon by G_T<=2T+6.
The number of first-merger pairs with
one such incoming top event and one
low-gain partner is therefore O(R(J+1)).
Birth partners give O(R). This does
not bound pairs with a low-history
partner at an EARLIER small-label
merger, which later share a top event.

The remaining difficult classes in
(1),(9) include high-mass branches,
short-idle branches whose last arrival
has a small label but a long prior gain
history, simultaneous high/small branches
with large inherited mass, and earlier
small/small mergers on the pruned paths.
The sparse arithmetic estimates in
(12)-(17) do not bound those classes.

## 8. Small-label runs: exact phase capacity instead of maximum gap

For fixed z>=5 let P_z be all odd primes <=z,
Q_z their product. The restricted process on
any even position b and absolute tick n
absorbs after finitely many jumps, by the
spatial walls of 0116e3e. This is true also
on the formal periodic extension. Define
the nonnegative maximum of its completed
prefix net credit

    B_z(b,n)=max_(restricted prefixes, including empty)
                        (4 W_prefix-G_prefix).

It is a bounded periodic function of b mod
2Q_z and n mod 2Q_z. If the next restricted
winner is p,w and b'=b-p+1, n'=n+w, then

    B_z(b,n)=max(0,4w-(p-1)+B_z(b',n')).                       (18)

At a restricted absorber B_z=0.
The recursion is finite on each spatial
wall cell. It permits an exact calculation
for any fixed finite alphabet. Write B0(z),
B1(z) for its two mean values over all
even b mod2Q_z and n of the respective
parity mod2Q_z. These are UNCONDITIONED
arbitrary-phase means, not the canonical
root conditional-rough local moments.

Every actual contiguous completed low-label
run (p<=z), from any arrival state, follows
a prefix of the restricted process. A high
label can cut this prefix short but cannot
change its earlier low winners. Its net
credit is therefore <=B_z at the start,
even if the run has many events. For a
canonical root stopped at any completed
prefix (or during its final incomplete
wait, using its last arrival), the exact
height identity gives

    G = 12-4h+sum_events(4w-g)
      <=12+B_z(A,n_A)
             + sum_(high p>z) [ (4w-g)_+ + B_z(b,n) ].         (19)

Here (b,n) in the sum is the state AFTER
that high event. Unlike summing positive
credit of every small event separately,
(19) cancels the negative credit within
the low runs. It also bounds a truncated
low run by its maximum prefix credit.

There is an explicit actual-integer light
capacity coefficient. For fixed p>z put

    H(p)=E[(8 q-p+1)_+ | p divides a+/-1],

where the expectation is uniform even a
mod the primes <=p, with the specified
p pin, and q is the least eligible neighbor
prime. The two signs give the same law.
Writing V_*(x^-)=prod_(3<=r<x)(1-2/r),

    Pr(q=r)= (2/r) V_*(r^-) for odd primes r<p,
    Pr(q=p)= V_*(p^-).

So H(p) is an explicitly computable finite
sum. Because w<=2q, it bounds the mean
of a pointwise upper bound on incoming
positive credit. Mertens or the earlier
roughness estimate gives H(p)<<p/log^2 p.
Indeed the weight vanishes unless
q>(p-1)/8, and is <=7p+1.

Consider any choice of prefix per actual
root through its elapsed horizon T. Suppose
every retained physical firing key with
p>z has at most M participating retained
roots (M fixed). There is NO bound on
small-label masses. Then

    limsup_(R->infty) (sum_A G_prefix)/(N_R T)
             <= M C(z),                                      (20)
    C(z)=(3/2) sum_(p>z)
                       [B0(z)+B1(z)+2H(p)]/p^2.

Proof: use (19), summing root incidences at
each high key, majorized by M times the
pointwise bound (8q-p+1)_+ plus M times
B_z at the destination. Initial terms are
O_z(R). For fixed p and side, its potential
arrival keys b in [R-2T-6,2R], 0<=n+b/2<=T+3
with the two congruences (10) in (b,n)
(i.e. b=c mod2p and n fixed mod2p)
number asymptotically RT/(4p^2).
The low coordinate vector (b,n) is uniformly
distributed over even b and the prescribed
n parity mod 2Q_z: along the b progression
the fixed p is coprime to Q_z, and for each
b the allowed n interval has length T+3
with fixed step 2p. All fixed residue-class
boundary errors vanish relative to RT.
This yields B0 or B1 for that side. The
same fixed-prime CRT calculation on the
source coordinates up to p gives H(p).
The normalization N_R~R/6 gives factor 6/4.
For passage to the full prime sum, the
B_z tail beyond any fixed U is bounded by
O_z(RT sum_(p>U)1/p^2) using the unweighted
key count O(RT/p^2), since p<=2T+7.
For the credit tail use its necessary
(p-1)/8-roughness and upper weight O(p);
the two-form upper sieve gives
O(RT sum_(p>U)1/(p log^2 p)).
The latter tends to zero after dividing by
RT and letting U->infinity. Thus the
limit upper estimate (20) is valid; no
growing primorial transfer is required.

In particular the coefficient obeys

    C(z) << (B0(z)+B1(z))/(z log z) + 1/log^2 z.                (21)

If the average maximum restricted credit
were o(z log z), this would tend to zero.
That estimate is not proved. The finite
arbitrary-phase numerical diagnostics below
motivate it, but are not a proof even of
its limsup. The coefficient (20) is an
upper capacity, not an asymptotic for
actual root gain. For z fixed, it can be
used with a prefix stopped BEFORE its
first heavy high firing. Under hypothetical
finiteness of twins, the fraction of roots
having a full horizon among those prefixes
is at most 3M C(z)+o(1), using the earlier
G_T>=(1/3-o(1))T. This gives a conditional
contradiction route if a sufficiently large
light fraction and small coefficient are
proved. It does not bound the number of
roots that become heavy. No numerical
threshold claiming this contradiction
is justified by the finite experiments.

## 9. Audits and reproducibility

All three scripts were executed in the ECMAScript research
runtime, fetched from their exact remote commits, and
re-executed with identical counts. Reproduce with node.
No separate Node or Lean invocation.

A. research/min_local_negative_first_merge_cut_and_threshold_audit.mjs
   commit 10c83cb5063eecc42a737895775aea9609b24bb5
   blob 715c8279e848947759ffc961aea4296c77b9fea9

All canonical roots in R=3000,12000,48000,192000,480000
at T=ceil(8sqrt(2R+1)). Store each root's occupied
post-tick interval at a position, including its birth
and retirement ticks. Sweep each position by interval
start and retirement time. Count first mergers by (1)
and independently count removed pairs at retirement.
At R=3000 independently scan all unordered root pairs
for overlapping occupancy intervals. Also compute
first-crossing mass and energy at J=0..128 and verify
the pair interval-overlap identity (2) including
finite-window clipping, and assigned-grid (3).
Five concrete nonnested gain-cut counterexamples found.

    roots                                      122505
    completed events                          3262121
    occupancy intervals                       3384626
    sweep groups                               548556
    incoming divisibility checks              3262121
    simultaneous branch-pair checks               9183
    pr>T+3 reset checks                            533
    independent root-pair scans                 125250
    energy balance checks                            5
    threshold controls                              645
    interval pair-overlap checks               5299667
    assigned-grid controls                      357657
    top-slow / idle-age checks                    2271
    reset-idle controls                         141656
    short-lag high/high checks                      68
    staggered reset checks                          68

All assertions passed. Whole-horizon merger ledger:

    R        P total    birth      idle       jump/jump
     3000       4312       945       3180         187
    12000      30660      4868      23867        1925
    48000     183809     23216     147208       13385
   192000    1193341    114266    1003252       75823
   480000    3522492    295826    3016909      209757

At R=480000, T=7839, 80001 roots, top means p>=ceil(T/16)
=490 and the finite idle age cutoff K=floor(sqrt T)=88.
There are 20537 first-merger pairs with incoming top
slow incidence and idle partner: 8848 with age>=K,
11647 with short idle and preceding small arrival,
42 with short idle and preceding top arrival. All 42
are staggered reset pairs (two distinct lagged keys).
There were 13 incoming keys with top slow and long
idle; no top/top simultaneous pair with both slow
incidences in these five finite controls. The finite
age cutoff is used for testing the identities, not
for an asymptotic sieve experiment.

B. research/min_local_negative_future_slow_pruned_mergers_audit.mjs
   commit 94e01cdde78562e4fc0afb8647bea6b0404ca7b0
   blob e11a38b505abb2ab68221581e55f61c03f5edc1c

Same five slabs, top cutoff p>=ceil(T/16).
For every slow key list its participating slow roots.
Deduplicate unordered pairs over all these keys,
find their earliest overlap of physical occupancy
intervals by independent two-pointer scans,
classify their actual first merger, and check (6)-(8).

    slow top incidences                         42267
    slow top physical keys                       2538
    pair incidences over keys                  1429115
    distinct pruned pairs                      1064787
    first-merger search steps                 40667717
    weighted-energy checks                     1064792

All assertions passed.

    R       all first-merger P     pruned P_I   first both labels small*
     3000           4312                 799                 699
    12000          30660                6240                5637
    48000         183809               41232               40100
   192000        1193341              317716              296353
   480000        3522492              698800              682960

* At the first merger both most recent arrival labels
are below the top cutoff, with birth label encoded as 0.
This does not mean both gains are small.

For R=480000 the pruned first-merger branches consist
of 72933 birth pairs, 579463 idle/jump pairs, 46404
jump/jump pairs. 339780 have smaller post-gain <=66
at first merger, 359020 have both >66. Mean gain of
the larger root at its first merger in the pruned
pair population is 1121.397..., of the smaller
227.219... . These are pair-weighted quantities.
There are 1409 top slow keys, 25535 slow incidences,
sum s_e^2=1921619, sum g_e s_e^2=1476968238 and
sum g_e=1088940 over those keys.
The observed mean total gain/T=909.13699/7839=.11598...
is below 1/3, but a finite slab observation.
The pair pruning removes many irrelevant merges,
yet almost all retained first mergers occurred
before either most recent arrival had a top label.
Consequently the sparse top/top merger bounds alone
cannot establish (9).

C. research/min_local_negative_low_run_phase_capacity_audit.mjs
   commit cea76ac002a5bf659f93cf92e82865108bff9ac8
   blob 213027bd4e0fe5a72b2602969dfe66f681d7b5ce

Exact dynamic programming on spatial period x=b/2
in [0,Q_z-1] and n mod2Q_z for z=3,5,7,11.
The x=0 wall prevents crossing the left boundary;
all nonzero jumps strictly decrease x. Compute
restricted absorption gain and B_z by (18).
Compare with direct simulation on a deterministic
subsample of states. The z=3 computation is a
control; (19)-(21) stated for z>=5.

    exact phase states                         2690568
    restricted transitions                     2375472
    independent direct simulations                2653

Exact finite phase means (rounded display):

    z     Q_z       B0(z)       B1(z)      max B_z
     3        3       8.66667      8.66667      24
     5       15      19.84889     20.06222      66
     7      105      34.39565     34.69043     196
    11     1155      47.73497     48.02344     448

Sample arbitrary-phase independent uniform residue
environments for z=11,31,127,511,2047,8191, with gain
cap 64z. All 9216 sample paths absorbed before cap
(126366 events); this is not a deterministic bound.
For the coefficient H(p) compute the least-factor
distribution through p<=2000000, using prefix sums
and 30 independent direct expectation checks.
Report only a PARTIAL sum of the infinite coefficient.

    z     samples  (sample B0+B1)/(z log z)  partial C(z)
     11     2048          3.49505                 5.21265
     31     2048          2.24898                 3.07018
    127     2048          1.09618                 1.73436
    511     2048           .61369                  .99576
   2047      512           .31697                  .54863
   8191      512           .20978                  .36019

For exact z=11 the partial coefficient is 5.33294.
The sample partial sums are not upper bounds for
C(z), because their low phase means are estimated
and the prime sum omits its nonnegative tail.
No rigorous coefficient <1/3 has been obtained.

## 10. Remaining proof

The exact gain-crossing overlap corrects the naive
nested-partition approach. The physical merger ledger
and pruned weighted energy reduce the required
large-slow supply estimate to only the pairs that
matter to subsequent high firing. Sparse high/high
simultaneous and short-lag nonreset collisions, and
the long-idle four-form sieve, control corresponding
light branch populations. The exact arbitrary-phase
low-run capacity gives a new small-label tool, but
its uniform coefficient and the mass of heavy
cohorts are still open. Most pruned first mergers
in the finite controls involve only labels below
the top band; this identifies the remaining
scale-to-scale obstruction rather than a proof
of the desired energy bound. In particular (9)
and the actual mean upper bound below T/3 have
not been established. No twin-infinitude proof,
Lean verification, or changes to canonical Lean
targets, sibling branches, or Context files.
