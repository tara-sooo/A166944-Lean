# Negative MIN: physical block entropy, birth compression, and virgin collision dilution

2026-11-27 JST. Continuation of 095053c3aa638a04afaa38d199a0d2e6152f6f9c.
Replace record-return edges by actual stationary clock blocks on the
selected near-square-root cohort. This gives two exact decompositions
of entropy, separating canonical births from jump arrivals. The birth
contribution is bounded by a logarithm of the mean event count.
Macroscopic-label mixing, including its binary mixing with low
arrivals, can also be made subleading under a coarse event-count
bound. For formal complete periods we derive a two-sided deletion
dilution inequality for first-use p incoming traffic mixing with
p-virgin idle traffic, even below record heights. No full asymptotic
event-count or entropy bound, selected mass lower bound, actual
large-height transfer, or Lean verification. Paper-level deductions.

## 1. Fixed cohort and stationary blocks

Use the selected actual slab of 095053c:
A in [R,2R], 6|A, K=floor(sqrt(R)/log^B R),
T=4K, J=floor(g T), fixed 0<g<2/9,
S={A:G_T(A)<=J}, N_s=|S|>0.
Let H=floor(3+T-J/2).
All selected paths have completed every event before
their common first postheight H for large R and
remain idle at their retirement positions through H.
The last event time W<=9J/4+8 ensures this for
large R, since 3+W<H. Use the common H cut,
not unequal absolute retirement times.

For a root trajectory define a stationary block as
its period at an unchanged position a, starting
at its canonical birth or a completed jump into a,
ending immediately before the next firing or at
the common cut H. It has key (a,u), where u is the
last absolute tick in that interval. Equivalently
use u+a/2 as the last postheight.
If two roots share a block key, their intervals
share the outgoing event (or terminal cut);
one can have entered the block later than another.
Their incoming groups are indexed by arrival
absolute time n and label p, with p=0 for birth.
For a nonzero p the incoming source is a+p-1,
and the sign is determined by the absolute parity.
At fixed a the two sign residue classes are
disjoint for odd p. The incoming group is exactly
the outgoing traffic of a preceding block with
end time n-1. All completed paths go to a smaller
position at each jump. No cycles or repeated
visits to a block by one root.

For f(t)=t log t, f(0)=0, let a block's total
mass be m and its entry-group masses m_i.
The information generated in this block is

    F(block)=f(m)-sum_i f(m_i).                 (1)

All internal f(m) cancel with outgoing groups
of other blocks. Each canonical birth has mass
one, and terminal block masses are precisely
the endpoint multiplicities. Therefore

    sum_blocks F(block)=N_s L,

L=(1/N_s)sum_a m(a) log m(a).
This is exact for actual physical times and
contains all record/nonrecord merging.

## 2. Physical-time decomposition and birth bound

Let Phi(x,y)=f(x+y)-f(x)-f(y) and
g0(x)=Phi(1,x)=(1+x)log(1+x)-x log x.
Within a block order its entry times.
At each n let U be resident mass from strictly
earlier arrivals, I total simultaneous jump
mass, and I_p each label's mass. If a selected
canonical birth occurs at n it contributes
a single root. The exact increment is

    Phi(U,I) + f(I)-sum_p f(I_p)
        + 1_birth Phi(1,U+I).                  (2)

This follows by expanding f(U+I+1_birth)
and cancelling f(U), f(I_p), f(1).
Summing in the block telescopes to (1).

The first term is resident/arrival mixing,
the second is simultaneous jump mixing,
the third is canonical birth mixing.
Births can be at most one per block:
at a fixed position a the canonical birth
time is 3-a/2, with 6|a. There are
exactly N_s selected birth events.

Let nu=E_S N_event be the mean number
of completed jump events, and let V be
the total mass U+I at all selected
birth ticks, normalized by N_s.
A given root can visit at most one
selected birth state in each block,
and its own birth is not included
in the resident/incoming mass at that
birth. Hence V<=nu. By concavity of g0,

    L_birth <= g0(V) <= g0(nu)
                    <= 1+log(1+nu).           (3)

This is an unconditional bound on that
component on any selected cohort.
It is not necessary that all roots
visit birth states of other selected
roots or that the set of selected
roots be closed under restarting.

Alternatively split (1) into a
birth option and all jump arrivals.
If a block contains a birth, its
contribution from mixing that one
birth with ALL jump arrivals to the
same block is Phi(1,m-1). This may
be larger than the actual-time birth
term (2), since it includes arrivals
later than the birth. Summing over
birth blocks, the normalized mass
m-1 is also at most nu: every root
has N_event+1 distinct blocks,
and its own birth block is excluded.
Thus this alternative birth term
also obeys (3).

In particular, if log(1+nu)=o(loglog R),
all birth mixing is subleading at
the entropy threshold of 54b0687.
For example nu=O((loglog R)^C) for
fixed C suffices. Such an actual
event-count bound has NOT been proved.

At a physical tick the arrival
postheight h satisfies p|h for
minus arrivals and p|h-3 for plus
arrivals, with the same absolute
parity for all incoming labels.
For h=0 no root can arrive by an
idle step from h=-1. Thus there
is no resident/arrival mixing at
height 0 in the physical decomposition.
For p>=5 a reset at h=0 is minus,
at h=3 is plus. Away from the
degenerate height factor (h=0
for minus, h=3 for plus), the
distinct incoming prime count is
at most omega(|h-c|), c=0 or 3,
and also at most omega(a) or
omega(a-2) respectively. Therefore
simultaneous entropy is at most
I log of the smaller of these
factor counts, for a positive
incoming mass. At a reset use
only the spatial factor count.
If two simultaneous labels are
>=Y with Y^2>max(h,|h-3|),
they cannot both be present
away from the degenerate reset.
For selected roots all arrivals
h<=11+7J/4 by the universal
wait potential. This locates
the high/high simultaneous
ambiguity at resets, without
asserting that all other mixing
is negligible.

## 3. Stationary-block label and arrival-time decomposition

Remove birth mass from (1), with its
separate mixing term as above. Group
jump arrivals by label p (sign unique
for a given target and odd p).
Let M_p be their total mass and M
the sum across labels. Then

    F_jump(block) =
       f(M)-sum_p f(M_p)
        +sum_p [f(M_p)-sum_n f(m_(p,n))].       (4)

The first term is label mixing,
the second is arrival-time mixing
within a label. At a fixed target,
arrival times of label p lie in a
single class modulo 2p. Thus each
is determined by its nonnegative
integer age index floor((u-n)/(2p)),
where u is block end time. Conditional
on p and block, the entropy of this
index is bounded by g0 of its mean.
Subtracting its minimum before taking
the mean leaves entropy unchanged and
gives a stronger bound. A single
arrival time has ZERO information
cost; charge only groups containing
two or more actual times.

For a nonterminal block, if q(a)
is the least odd prime factor of
a-1 or a+1, its length is <2q(a)
in time difference, since its
stationary interval cannot cross
any such clock. Consequently a
label p>=q(a) has at most one
arrival time. For p<q(a) the count
is at most 1+floor((u-d)/(2p))
where d is the last stationary clock.
The same statement holds for a
terminal truncated block, whose
actual interval is inside a single
clock block. This gives an additional
local cap by log of that count,
besides the mean-index bound.
All of these estimates count only
actual occupied branches. Bounding
their normalized weighted sum at
growing R is still open.

At terminal blocks each root enters
one block only. Thus terminal
label entropy alone is at most
log(max_a omega(a(a-2)))<=loglog R+O(1),
using even the elementary bound on
number of distinct prime factors.
This does not bound the arrival-time
component or the nonterminal labels.

## 4. Remove macroscopic labels including mixed high/low groups

Fix a cutoff Y>=5 and split all jump
entries in a block into high p>=Y
and low p<Y. Let their masses be
M_h,M_l, and let E_h,E_l be their
internal entropies, computed as in
(1) but within each population.
Exactly

    F_jump=Phi(M_h,M_l)+E_h+E_l.

Let alpha=E_S N_high, nu=E_S N_event.
Then alpha<=J/(Y-1), and the
normalized sums of high and low
arrival masses across all blocks
are alpha and nu-alpha. Concavity
and homogeneity give

    L_high-low <= Phi(alpha,nu-alpha).

It can be tightened by summing only
masses in blocks containing BOTH
populations.

At an arrival target a, at most
d_Y=2 floor(log(2R)/log Y)
distinct possible high odd primes
divide a or a-2. Arrival heights
are between 0 and 11+7J/4 and
one p's arrival times differ by 2p.
Hence the total high entry groups
in one block is at most

    Q_Y=max(1,d_Y(1+floor((11+7J/4)/(2Y)))).

This includes reset arrivals and
terminal blocks, without using any
maximum inherited cohort mass.
It follows that high internal
entropy is <=alpha log Q_Y.
Combining with (3) gives

    L <= g0(nu) + Phi(alpha,nu-alpha)
                + alpha log Q_Y + L_low,        (5)

where L_low is the internal entropy
of low jump entries of the FULL
selected paths, not an entropy
of a restricted MIN simulation.

For fixed c>0 and Y=cJ, J comparable
to sqrt(R)/log^B R, Q_Y=O_c(1)
and alpha=O_c(1).
If log(1+nu)=o(loglog R), the
first three terms are o(loglog R):
Phi(alpha,nu-alpha)<=alpha[
1+log(nu/alpha)] when alpha>0.
Bounded alpha permits even
alpha approaching zero. Thus the
macroscopic high population's
mixing, INCLUDING binary mixing
with low arrivals, and all birth
mixing are subleading under the
stated coarse event-count assumption.
This is stronger in scope than the
previous within-high-only O(1)
component bound; it is conditional
on the actual event-count estimate.

More generally if nu<=O((loglog R)^C)
and Y=J/L0 with L0>=1 satisfying

    L0=o(loglog R/logloglog R),

then d_Y=O(1), Q_Y=O(1+L0),
alpha=O(L0), and all three
terms are o(loglog R).
For the binary term one can use
Phi(alpha,nu-alpha)<=alpha log(e nu/alpha)
and alpha<=min(nu,O(L0)); this
is O(L0 log(2+nu)+1).
Consequently the sufficient entropy
coefficient of 54b0687 can be
sought entirely in L_low with
this cutoff, provided the mean
event-count estimate and selected
fraction lower bound are proved.
No estimate of L_low at this
asymptotic scale is established.

## 5. Two-sided physical first-use deletion dilution

This section concerns the FORMAL
complete CRT period, not the actual
growing-primorial slab. Fix a finite
odd-prime alphabet P containing 3,
p in P with p>=5, horizon T.
Let P^- be P without p. A uniform
canonical period has M=p M^- roots,
where M^-=2 prod_(q in P^-,q>=5) q.
Use cyclic spatial period L=6M
and index physical keys by (a mod L,h).
This is the quotient of simultaneous
spatial/time translation. One may
also choose a common fixed cohort,
with selected fraction s, in the
full period; counts below are first
normalized by the full M.

For a deleted root path through T,
count candidate SOURCE ticks C_s:
at preheight b and absolute parity
sigma, p divides the appropriate
height factor 2b+1 or |2b-5|, and
the deleted winner is idle or >p.
There is exactly one of its p lifts
with root residue such that
a=sigma mod p. At that lift p
would win IF its full path has
not used p before. Its corresponding
incoming target key is
(a-p+1,b-(p-1)/2).
The lift preserves parity.
Because p was not used previously,
every actual first-use p arrival
is among these candidate keys.

Count candidate BASE ticks C_b on
the deleted path: idle ticks with
postheight h>=1 and
h=0 mod p (minus parity) or
h=3 mod p (plus parity).
There is exactly one p lift with
target position a=sigma+1 mod p,
so the spatial and clock arrival
constraints for a hypothetical
p incoming jump both hold.
At this lift p is not itself
eligible at the target.
Every actual p-virgin resident
idle cohort at a potential p
arrival key coincides with its
deleted path through that tick
and is among these lifts.

Let S_p(a,h) be the actual first-use
p incoming mass, and B_p(a,h) the
actual idle resident mass which has
never used p, restricted to keys
with the required p arrival pins.
Both are bounded POINTWISE by the
respective candidate counts from
the lifted deleted paths. In
particular normalized total masses
are bounded by E_- C_s/p and E_- C_b/p.
The first is also <=1, since one
root has at most one first p use.
Any previous winning p test merely
removes candidates. Exact
certificates can prune such lifts
by the first matching pin on the
deleted history; no independence
between the two deleted profiles
is needed.

By the log-sum inequality we get

    (1/M) sum_(a,h) Phi(S_p(a,h),B_p(a,h))
       <= Phi(min(1,E_- C_s/p), E_- C_b/p)
       <= (1/p) Phi(E_- C_s,E_- C_b).            (6)

For a selected cohort, the same
bound holds divided by s when
normalizing by its size, with
candidate means still over the
unselected deleted period.
This includes first uses at
nonrecord heights, and uses
only one-path visit counts.
At height 0 the candidate base
count is zero, since an idle
postheight cannot be zero.

The quantity in (6) is the binary
submix of first-use p arrivals
and p-virgin resident mass,
NOT the entire physical entropy.
Previously p-used resident roots,
repeated p arrivals, and other
simultaneous branches may mix
with these groups. Sums over p
need care because the virgin base
mass can occur in multiple submixes.
No independent factorization of
the two deleted profiles or
actual square-root CRT transfer
is claimed.

The source count is bounded by
the deleted height-visit count at
p-clock preheights; the base
count by its idle-height count
at p arrival heights. The latter
has the exact descent occupation
identity of 326eb62. Thus (6)
connects the new entropy analysis
to the earlier one-path height
occupation theory. The unpruned
visit bounds can be loose when
a root revisits the same pins
many times; the numerical test
below shows this explicitly.
A possible next step is a
first-pin-pruned visit moment
rather than a cross-profile
second or third moment.

## 6. Executed audits

Both final scripts executed in
the ECMAScript research runtime,
fetched from exact remote commits
and re-executed with matching
outputs. Reproduce with node.
No separate Node/Lean invocation.
No new external literature claims.

A. research/min_local_negative_physical_block_entropy_audit.mjs
commit d7dc214a0368181cb56e3d60dc46270d19e95b24
blob 45bf0a7f73b31d6d7223d329753147c3e14c8f90

Actual slabs R=12000,48000,192000,480000,1000000,2000000;
B=1/2, g=1/5. Independently build
physical blocks from selected paths,
check traffic and exact time-ordered
and label/time decompositions.
Check birth count, factor clock pins,
Jensen birth bound, shifted geometric
age bound, high/low split and
gain/event budgets. Counts:

    roots                      622004
    full completed events     14181783
    selected roots             207261
    distinct blocks            486990
    entry groups               667639
    block entropy checks       486990
    incoming clock checks      460378
    selected birth checks      207261

    R         L         resident      simultaneous    birth
      12000   1.139180   .636912      .042088         .460181
      48000   1.531841   .854979      .068874         .607988
     192000   1.929866  1.124813      .094852         .710201
     480000   2.217536  1.300513      .130841         .786182
    1000000   2.412018  1.423916      .158677         .829425
    2000000   2.621099  1.577308      .177688         .866103

At the largest R, 115899 selected,
nu=8.05027, V=1.49943,
g0(V)=1.68224, g0(nu)=3.14539.
Resident/arrival collision masses
A=1.38515 and B=1.72838 (normalized),
not the record-level masses of 095053c.
The simultaneous term away from
heights 0 and 3 is only .00036308;
the rest .17732458 is at those
heights. No general zero assertion.

Alternative block decomposition:
birth=1.2249466, label=.7755149,
time=.6206372. Terminal total=.8955032,
terminal label=.2219199, time=.4069883,
birth=.2665950. The collision-only
shifted age upper is 1.8122851
instead of unconditioned 8.1314262.
The occupied label-count upper
is 1.0931059.

For cutoff Y=148=floor(J/2),
alpha=.05750697, high/low entropy
=.02737396, high internal=.00047652.
Their aggregate collision-conditioned
bound using maximum occupied high
groups is .07575314.
At Y=74 and 37 their actual sums
are .08063406 and .21870843,
respectively. These are finite
diagnostics, not asymptotic estimates.
Some unused zero diagnostic fields
(e.g. liveClockEntropy) in the
script are not used as evidence.

B. research/min_local_negative_physical_virgin_entropy_audit.mjs
commit 89586b97bd07fee335898ba8f5e98c064528db29
blob 9fe5c294755b60af6b638af6b222de08e030f982

P={3,5,7,11,13}, M=10010;
p=5,7,11,13 and T=24,40,64.
Independently simulate full
period roots and deleted period
roots. Construct unique CRT lifts
for every candidate tick. Compare
pointwise actual p-first and
virgin-resident masses to deleted
candidate masses and (6).

    full period root controls    120120
    deleted root controls         15336
    tick updates                5779456
    source lift controls          95137
    resident lift controls        89065
    pointwise mass controls       74254
    entropy comparisons              12

All assertions passed. At T=64:
 p    actual submix    unpruned bound (6, last)   matched-mass bound
 5       .0141453             3.482782              .0144644
 7       .1299440             1.760550              .1383272
11       .0071886              .707124              .0074966
13       .0759993              .492674              .0843919

The candidate lift bound is valid
but very loose in these repeated
small-prime controls. The smaller
matched-mass bound still uses
actual simultaneous presence at
a collision key, not a separate
estimate of that presence.

## 7. Remaining target

There are now two exact entropy
ledgers, record returns and physical
stationary blocks. The latter
isolates one birth per root and
offers the logarithmic compression
(3). A coarse subpower-of-log
mean event count would remove
birth and macroscopic-label
mixing from the leading coefficient
by (5). The remaining low entry
mixing in full physical blocks
and the selected-population
fraction need asymptotic estimates.
The two-sided physical deletion
bound (6) supplies an approach
to first-use/virgin submixes
without a cross-profile correlation
bound, but repeated labels and
actual CRT discrepancy are not
controlled. No proof of the
coefficient below 3 or twin
infinitude, no Lean verification.
No canonical target, sibling
branch or Context changes.
