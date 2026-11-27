# Negative MIN: mean height profile, small-descent landing localization, and proof targets

2026-11-27 JST. Continuation of 326eb625274972fde98709d37641d766241c883b.
The user asked to examine in detail how to prove the downward-overlap
bound, rather than simply restating it as the next goal. We show
that the expected squared pathwise overlap is stronger than needed.
A squared MEAN profile, or just its mass on sparse high-clock heights,
suffices. A finite-alphabet run decomposition reduces the latter
to arrival-height concentration for finitely many fixed labels;
arbitrarily large initiating labels can be discarded by their gain
cost. We give explicit finite-alphabet constants, diagnostics and
concrete alternative sufficient criteria. The limiting concentration
estimate, the full mean-gain saving, and the growing-period actual
transfer remain unproved. No Lean verification or literature
priority claim.

## 1. Replace mean squared overlap by squared mean profile

Use the height occupation identity of 326eb62:
on any completed prefix of the low-only process
with cutoff Y, initial height 3, each nonidle
firing e contributes its interior descent interval

    I_e=[b_e+1-(p_e-1)/2,b_e-1] intersect Z.

Its length is (p_e-3)/2; p=3 contributes nothing.
Define D_z(b)=sum_(e:p_e<=z) 1{b in I_e}, and
m_z(b)=E D_z(b) under the formal canonical root
distribution (or under the actual slab distribution,
for a deterministic height bound).
The high-clock weight beta_Y(b) is deterministic,
and for Y=cT, fixed c>0, sufficiently large T,

    0<=beta_Y(b)<=2/Y,
    sum_b beta_Y(b)^2 <<_c 1/(T log T).
    B={b:beta_Y(b)>0}, |B|<<_c T/log T.           (1)

The last statement follows by counting primes
Y<p<=2T+7 and their O_c(1) possible clock heights.
All such heights are >=(Y-1)/2.

The small-label expected toll is exactly

    E W_<=z = sum_b beta_Y(b) m_z(b)

and hence

    E W_<=z <= (sum beta_Y^2)^1/2
                              (sum m_z^2)^1/2. (2)

Thus the sufficient small-label condition in
326eb62 can be weakened from
E sum_b D_z(b)^2=o(T log T) to

    sum_b (E D_z(b))^2=o(T log T).                (3)

This is a second moment of the mean occupation
profile, not the expectation of a second moment.
Jensen gives the implication in the correct
direction. Rare trajectories with large local
time need not force (3) to fail.

In fact the exact condition needed for the
small-label toll in the existing proof is
even more targeted:

    sum_(b in B) m_z(b)=o(T),                    (4)

for each fixed z, with c fixed. It is a sufficient
condition since beta<=2/Y. The total sum m_z
is <=T+3, by the height identity and the gain cap,
so (4) is a nonconcentration problem on a sparse
deterministic set, not a request for o(T) total
gain. The longer descent intervals of labels >z
are handled by the deterministic short-interval
upper density estimate of 326eb62 section 4:
their total toll is <=C_c epsilon((z-3)/2), where
epsilon(L)->0 as L->infinity.
Take T->infinity first and then z->infinity.
Thus (4) for every fixed z gives
Pr_formal(any p>cT)=o(1) and expected total
gain from those high labels o(T), including
all later repeats. On actual integers the same
toll bound holds, but the positive-part
single-prime discrepancy Delta_R from 326eb62
must still be controlled separately.

Another sufficient form: if for some M=M(T)
with M=o(log T),

    sum_(b:m_z(b)>M) m_z(b)=o(T),

then sum_B m_z <=M |B|+o(T)=o(T).
This makes it unnecessary to prove a uniform
bound at every height. A bounded L^(1+delta)
mean profile, sum_b m_z(b)^(1+delta)=O(T),
any fixed delta>0, also gives (4) by Holder.
The stronger but simple alternative
E N_<=z(T)=o(T), where N counts nonidle
labels <=z, implies (4) immediately by
sum_b D_z(b)<=((z-3)/2)N_<=z (z>=3).
None of these limiting estimates is proved
here; they are different sufficient targets.

## 2. Fixed-alphabet runs give explicit landing localization

Fix z>=5. Let P_z be the odd primes <=z.
For an arbitrary even position and arbitrary
integer absolute clock, consider the P_z-only
restricted process until it absorbs at a
P_z-rough position. Its finite congruence
extension has the spatial wall of 0116e3e:
Q_z=prod P_z, total gain <=2(Q_z-1).
Each completed wait is <=2p<=3(p-1),
so total elapsed time to last firing is
also bounded. Hence the following finite,
periodic constants exist:

    K_z = maximum total absorption gain,
    W_z = maximum total completed wait,
    C_z = maximum over starting phases and
          relative heights of the count of
          interior descent intervals covering
          that height in a full restricted run.

For example K_z<=2(Q_z-1), W_z<=3K_z,
C_z<=K_z/2. All maxima are computable
over (a mod 2Q_z even, n mod 2Q_z).
Using a redundant spatial period 4Q_z
is also valid. The bounds apply to
any prefix of a restricted run.

Now split ANY actual or formal trajectory
into maximal consecutive completed events
with labels <=z, cut by each event p>z.
Every such run is a prefix of the
P_z-restricted process from its starting
state. Indeed an earlier high firing may
truncate the run but cannot change an
earlier low winner. Include the first run
from the canonical seed and the last
possibly truncated run. If a run starts
at postheight h, each of its small descent
intervals is contained in

    [h-K_z/2, h+W_z].                             (5)

Reason: at any event the height differs
from h by elapsed time minus half the
accumulated gain. The endpoints of its
interior descent interval lie between
its postheight and preheight.
Its contribution to D_z at any one
height is at most C_z. Its total
descent length is <=K_z/2.

For p>z let N_p(h) count completed events
of label p with postheight h; put
N_>z(h)=sum_(p>z) N_p(h).
Every low run except the initial run starts
at the postheight of one such event.
Empty runs may be included, only increasing
the following upper bounds. From (5),

    D_z(b) <= C_z [
        1{b in [3-K_z/2,3+W_z]}
       +sum_(b-W_z<=h<=b+K_z/2) N_>z(h)].        (6)

This is a pathwise convolution bound on
the full trajectory, with arbitrary
preceding gain and repeated firings.
It applies equally to a low-only
trajectory at any larger cutoff Y.
It is not an independence assumption.

Let L_z=1+W_z+K_z/2 (all gains are even).
For instance Young's inequality on the
finite integer line, extending by zero,
and (6) give

    sum_b (E D_z(b))^2
      <=2 C_z^2 [L_z+L_z^2 sum_h (E N_>z(h))^2]. (7)

A pathwise analogue bounds sum D_z^2
by the same expression with N_>z^2
inside expectation. The mean-profile
version is the weaker relevant target.

More useful is the localized L1 bound.
For a set B of heights let

    B_z={h: [h-K_z/2,h+W_z] intersects B}.

Each low run contributes at most K_z/2
descent length on B and contributes
nothing unless its starting height
belongs to B_z. Therefore

    sum_(b in B) D_z(b)
        <= (K_z/2) [
                1{3 in B_z}+sum_(h in B_z) N_>z(h)].         (8)

This bound does not use the number of
mergers between different roots, nor
does it require a per-height second
moment.

For B the high-clock set of section 1,
fixed z, |B_z|<=L_z |B|=O_(z,c)(T/log T).
For large T, 3 not in B_z, since the
minimum high-clock height grows
proportionally to T. The enlarged set
lies in macroscopic heights, away
from the reset heights 0 and 3.

## 3. Eliminate all sufficiently large initiating labels

For fixed K>z the number of events
with p>K is <=(2T+6)/(K-1)
on any trajectory. This follows
solely from the total gain cap.
Split (8) by these labels and
the finitely many z<p<=K:

    (1/T) E sum_B D_z
       <= (K_z/(2T)) sum_(z<p<=K)
                           sum_(h in B_z) E N_p(h)
           + (K_z/(K-1))(1+3/T).                (9)

The constants K_z, W_z, C_z here
depend on the TARGET small alphabet
z, NOT the secondary cutoff K.
This order of quantifiers matters.
If, for every fixed prime p>z,

    sum_(h in B_z) E N_p(h) = o(T),              (10)

then take T->infinity with z,K
fixed and subsequently K->infinity.
This proves (4) for the fixed z.

In particular it suffices that
for every fixed prime p the
arrival-height mean profile is
uniformly integrable on the
macroscopic height scale:

    for all S_T subset [0,T+3] with |S_T|=o(T),
         (1/T) sum_(h in S_T) E N_p(h) ->0.      (11)

Only S_T=B_z is needed in (10);
(11) is a convenient stronger
criterion. It is still considerably
weaker than a pathwise uniform
local-time estimate for all labels.
The set of fixed prime labels in
(9) is finite before taking each
limit, so there is no hidden
uniformity in p required.

An explicit sufficient bound for
(10), by Holder, is for each fixed p
some delta>0 (may depend on p),

    sum_h (E N_p(h))^(1+delta) <<_p T.

It yields O_(p,z,c)(T/log^(delta/(1+delta)) T)
on B_z. A bound sup_(h in B_z) E N_p(h)
=o(log T) is another sufficient condition.
A proof of (10) could use the
arithmetic of fixed-prime arrivals:
minus p has p|h and p|a at arrival,
plus p has p|h-3 and p|a-2. At a
fixed h and fixed sign the source
or target positions form a single
class modulo 4p. Distinct same-height
same-sign p arrivals therefore
have at least 4p gain and at least
2p elapsed ticks between them
(the latter from the height identity).
For one fixed p, a given h, and
a fixed sign these repeat intervals
are disjoint along a path.
This is useful for separating short
and long return episodes, but
does not bound their aggregate
probability. A long elapsed gap
can involve many other heights
and smaller labels; CRT on p
alone does not give a fresh
independent trial for its repeat.

For a future return analysis
write E N_p(h)=sum_(j>=1)
Pr(N_p(h)>=j). The part j<=M
in the sum over B_z is at most
M|B_z|. It suffices to show the
remaining mean tail summed over
that sparse set is o(T), for
M=o(log T). This is a precise
return-tail goal, without assuming
a uniform geometric escape
probability conditional on an
arbitrarily exposed history.
In particular an argument
about a single local escape
from a height band must also
control later returns from
outside that band.

## 4. A deterministic finite-alphabet alternative

For z fixed and K>=z, define
A_z(K) as the maximum TOTAL
interior descent length from
labels <=z in a full P_K-only
restricted absorption, over
all arbitrary initial phases.
It can be computed by exact
finite-state dynamic programming.
For a restricted first event
of label p,w, the value function
satisfies

    A(state) = 1{p<=z}(p-3)/2
                       + A(next state),

with zero at an absorber.
The spatial walls make the
recursion acyclic on each cell.

Splitting any trajectory at
events >K yields

    sum_b D_z(b)
       <= A_z(K) (1+N_>K)
       <= A_z(K) (1+(2T+6)/(K-1)).               (12)

Thus liminf_(K->infinity) A_z(K)/K=0
for every fixed z would give
o(T) total small-label descent
deterministically, hence (4).
This is a genuine finite-alphabet
sufficient criterion, not a proved
asymptotic. In small exact periods,
the maxima increase faster than
the uniform phase means, and
A_7(K)/K increases from .4 at
K=5 to 1.727 at K=11.
Consequently there is no present
numerical basis for assuming
the worst-case criterion.
The mean arrival profile route
(9)-(11) is less demanding than
proving (12) small for every phase.

## 5. Audit and diagnostic results

Both scripts were executed in the ECMAScript
research runtime; exact remote readback and
re-execution were carried out for each.
Reproduce with node. No Lean invocation.

A. research/min_local_negative_small_descent_landing_profile_audit.mjs
   commit 1959af57e3914529ca87cbe227187aa0ff5de620
   blob b487a56d5be9b8c41be2f0c2ab051531b45905c2

Compute exact arbitrary-phase maxima for
P={3,5,7} on the redundant period
a mod 4Q (even), n mod 2Q, Q=105.
All 44,100 states yield

    K_7=34, W_7=56, C_7=2.

These are exact finite maxima (not
a bound for a growing alphabet).
Then sample coherent formal low-only
environments at Y=ceil(T/4),
T=1024,4096,16384,65536, with
384,384,192,96 independent
pseudorandom initial-coordinate
samples. Verify each small run
and the pointwise convolution (6)
and localized bound (8), using
these finite constants.

    sampled paths                           1056
    tick updates                        11403264
    local convolution checks            11406432
    restricted-run checks                  11215
    localized sum checks                    1056

All assertions passed.
For each height the sample mean m_hat
and its square are computed; also
report the distinct-sample pair
estimator of sum m^2:
sum_b [(sum_i D_i(b))^2-sum_i D_i(b)^2]
      /[n(n-1)].
It removes the finite sample diagonal,
rather than treating the paths as
a complete population. No asymptotic
confidence claim is made.

    T        mean sum D_7^2   pair mean-profile L2    mean sum D_7
     1024       7.91667           .87882                6.33333
     4096      14.43750          1.67122               10.91146
    16384      20.91146          2.35815               15.22396
    65536      28.97917          2.74518               22.22917

At T=65536 the mean full downward
overlap (all labels <=Y) is
6747.7083, mean small toll from
p<=7 is .00003677. Mean number
of p>7 arrivals in B_7 is 2.11458,
including 1.58333 with p<=127
and .53125 with p>127.
Mean sum of D_7 on B itself
is .86458. These are finite
samples, not a proof of (10).
At these finite T the expanded
B_7 can cover much of the
height range (57391 of 65540
heights at T=65536); the
asymptotic sparsity statement
is not numerically verified by
these percentages. The output's
unused meanSmallRunGain field
is zero and is not a diagnostic.

B. research/min_local_negative_small_descent_capacity_audit.mjs
   commit e947c05a2df8334adf0a6a0c203ce4ad237fdbce
   exact blob recorded by remote readback.
   
Use the wall at a/2=0 with the
spatial period Q and time period
2Q, processing increasing
positions and recursively
computing absorption gain and
small descent lengths for z=5,7.
Independent deterministic
subsample replay checks:

    states                            2690568
    nonidle transitions               2375472
    independent direct checks            2653

    K    max gain    A_5(K)    A_7(K)    phase mean z=7
     3       4          0         0         0
     5      14          2         2          .46
     7      34          3         8         1.52998
    11     104          7        19         1.78981

The phase mean is uniform over
arbitrary restricted starting
phases, not the biased actual
arrival distribution. Using
it in (12) requires a separate
bound on that distribution.

## 6. Recommended proof order and limits

The goal is to prove a new
anti-concentration estimate,
not to assume all height
local times are small.
Start with fixed labels p=5,7
and the mean profile in (10)
or (11), where same-height
return spacings are explicit.
Use the finite-run
decomposition to handle short
episodes, and seek a tail bound
for longer return episodes
under the coherent CRT law.
A successful bound for every
fixed p, with constants allowed
to depend on p, then proves
(4) via (9). By the long
descent density estimate it
proves macroscopic high-label
gain o(T) on the formal model.
The deterministic finite
capacity route (12) is a
separate testable alternative,
but the current finite maxima
do not favor it.

Even this would not alone
establish full mean gain
o(T) or <T/3: labels below
each macroscopic cutoff can
accumulate, and actual
one-prime discrepancy must
be bounded for the full
growing low alphabet. The
original stronger overlap
bound E Z_T=O(T) is not
proved or required for
this narrower supply step.
No twin-prime proof, Lean
verification, or canonical
target changes. Context
left unchanged per user
writeback preference.
