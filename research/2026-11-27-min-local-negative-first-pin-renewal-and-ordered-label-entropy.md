# Negative MIN: first-pin renewal, repeat gain budget, and ordered label entropy

2026-11-27 JST. Continuation of 589743f0b9cb06b5cdf28f50537d30650e2bbf87.
Replace the repeated tick exposures of the previous virgin-dilution bound
by distinct root pins and whole stationary blocks. The first-use incoming
block and the virgin lower-label block profiles can both be recovered
exactly from one-prime-deleted paths in a complete CRT period. A stopped
event-to-event renewal formula gives the signed insertion difference in
mean event counts, including a first firing that would exceed the gain
budget. Combine repeat spacing with first-pin probabilities to bound
event counts by single-prime deletion statistics. Finally telescope
the entire stationary-block label entropy in increasing label order
and separate its first-use/virgin, first-use/used, and repeat terms.
The exact identities and finite computations do not establish the
required asymptotic event count, entropy coefficient, or actual transfer.
Paper-level deductions, no Lean verification.

## 1. Distinct pins at whole stationary blocks

Use the negative MIN conventions of 589743f. Fix a finite odd-prime
alphabet P containing 3, p in P with p>=5, P^- = P without p.
For complete canonical periods put
M^- = 2 product_(q in P^-, q>=5) q, M=p M^-,
spatial period L=6M. A lift from a deleted root is A+k*6M^-,
0<=k<p; parity of the absolute clock is unchanged.

Run the deleted path up to the first POSTheight H>3 (all finite
restricted paths reach H by the spatial wall). At the beginning
of each stationary block, let a=A-G, n=h-a/2, and let the next
deleted winner have (wait w, label q), with w=infinity for an
absorber. For each sign sigma in {-1,+1}, the required root pin
is r=G+sigma mod p. There is exactly one lift with a=sigma mod p.
At that lift compute the first p-clock wait from the lifted
absolute clock, using c=0 for minus, c=p+2 for plus.

The candidate p event wins before the deleted block ends iff
its wait is <=H-h and its pair (wait,p) precedes the deleted
winner in lexicographic order. This includes a tie won by p<q.
Only the earliest p clock of that sign is needed within the
block. Scan the blocks in trajectory order and keep each root
pin only at its FIRST winning candidate. Write D_p for the
set of retained pins, d_p=|D_p|. Each pin represents precisely
one full-period root lift whose first p firing occurs at this
candidate: before it, all earlier p candidates have failed.
Unretained lifts follow the entire deleted path unchanged.

In particular, with N^- the number of deleted completed jumps,

    Pr_P(p used before H) = E_- d_p / p,
    d_p <= min(p, 2(N^-+1)).                       (1)

The equality includes all nonrecord p uses. It does not require
p to be the largest label. The number of candidate ticks in
589743f can be arbitrarily inflated by repeated clocks; the
right-hand side of (1) uses the number of distinct pins only.
It is an exact one-prime deletion formula, not an assertion of
independence of first uses of different labels.

## 2. Exact first and virgin stationary block profiles

Use the physical blocks of 589743f, now ending just before
a firing or at the common first postheight H. Identify a key
by (a mod L, u), where u is its ending postheight. The end
absolute clock is u-a/2, so this is equivalent to the physical
clock-block key modulo the common translation.

After a p jump the target is a'=0 mod p (minus) or 2 mod p
(plus). For p>=5 neither class is eligible for p itself.
Thus the stationary block entered by a first p firing is
determined completely by the deleted alphabet and its actual
post-jump state, even if its next jump belongs to some q>p.
For each retained pin from (1), calculate that post-jump
state and find the next deleted wait w'. The source's full
arrival block ends at u=min(H,h'+w'-1). Counting these
lifts gives EXACT first-p incoming block mass F_p(a',u),
without simulating the rest of the full path.

Conversely take any deleted stationary block starting at
gain G, position a, entry label q (0 for a birth).
There are two p-ineligible target-pin lifts with a=0 or 2
mod p. For each, test whether its root pin was retained as
a winning p candidate before or at entry into this block.
If not, that lift has never used p and enters precisely
the same block in the full process. At the target p is
ineligible, so no p firing can preempt its block exit.
This is an exact bijection to the p-virgin block entries
at p-compatible target positions. In particular, retaining
only entry labels 0<q<p gives the EXACT lower-label virgin
mass B_p^0(a,u) used below. Counting the unpruned lifts gives

    (1/M) sum F_p = E_- d_p/p,
    (1/M) sum B_p^0 <= 2 E_- N^-_(<p)/p,          (2)

where N^-_(<p) counts completed deleted labels <p.
If births are included, replace N^-_(<p) by N^-+1
for an upper bound on the broader base profile.
There is no repeated charge proportional to the length of
a waiting block. Pruning the first pins gives equality
of both profiles, not just pointwise dominance.

For Phi(x,y)=(x+y)log(x+y)-x log x-y log y,
with zero terms interpreted continuously, the formal
first/virgin lower-label mixing is therefore bounded by

    V_p=(1/M)sum Phi(F_p(a,u), B_p^0(a,u))
       <= (1/p) Phi(E_- d_p, 2 E_- N^-_(<p)).     (3)

It can also be calculated exactly from the two pruned
deleted profiles. No full continuation after first p
is needed for the unselected common-height cohort.
For a selected subcohort of fraction s, its profiles
are pointwise dominated by the unselected profiles;
(3) then divided by s is an upper bound. Exact equality
for selected profiles requires checking the selection
condition on the individual continuations. This does
not transfer the equality to an actual finite slab.

## 3. Gain-budget stopping and signed renewal for the event count

At common first height H, impose gain budget J>=0.
Stop BEFORE the first otherwise winning jump that would
make cumulative gain exceed J, or at the first postheight
H if reached earlier. Denote completed jump count N_J
and gain G_J. A full-height success is exactly a root
with unrestricted G_H<=J. This stopped rule never
executes the overshooting jump.

For a deleted path run to its own stop, use the
event-to-event scan of section 1. Its last block still
includes the candidate tick of its otherwise winning
unaffordable jump. A p candidate can preempt it.
For each first retained pin r, record pre-gain g_r,
the deleted prefix jump count, and whether
g_r+p-1<=J. Unaffordable first p candidates are
retained in the set of tested pins, even though their
jump is not counted: that full lift stops there and
cannot be activated by a later candidate on the
deleted path. Denote affordable first pins by D_p^ok.

For each retained pin r, start the full continuation
at the first p event; if unaffordable stop just before
it. Let N_r be the resulting TOTAL stopped count,
including the identical prefix. Lifts not retained
have N_J=N^-_J. Consequently

    E_P N_J - E_- N^-_J =
       (1/p) E_- sum_(r in D_p) (N_r - N^-_J),    (4)

    Pr_P(N_(J,p)>0)= E_- |D_p^ok|/p.            (5)

The same identity (4) holds for any statistic of
the stopped path by replacing the counts with its
values. For example indicator of reaching H gives
the exact signed insertion change of the selected
fraction, and count of post-first lower arrivals
gives the used-resident incidence in section 5.
No monotone coupling of event counts is assumed.
Some activated lifts have fewer events, as the
audit confirms. Retaining both signs and the
unaffordable first pins is necessary.

This is a reduction to one old path per old class
and continuations for the distinct active pins;
it is not a closed asymptotic recurrence for
E N_J. The number and costs of active tails still
need control when the alphabet grows.

## 4. Repeat gain spacing and mean count bound

Recall the same-prime relay spacing from 755b0ce.
For p>=5 two successive p events have signs sigma,
tau in {-1,+1}. If E is the total intervening gain
from non-p events, the first target is sigma+1 mod p
and the second source is tau mod p, so

    E == sigma+1-tau mod p,
    sigma+1-tau in {-1,1,3}.

E is nonnegative even, hence E>=p-1. This is
stronger than using p-3 as a relaxed lower bound.
For a fixed p the intervening intervals are
disjoint in event order. If its first firing has
pre-gain g_r and there are k p firings by the
stopped cut, then

    G_J-g_r >= (2k-1)(p-1),
    k <= 1+floor((J-g_r-(p-1))/(2(p-1)))         (6)

when k>0. In particular p>(J/3)+1 cannot be
reused on a gain-capped path. The gap charges
cannot be summed over different p as disjoint.

The canonical root has a=0 mod3. A consecutive
p=3-only run after a label >3 contains at most
two jumps: each reduces a by 2, and reaches
0 mod3 within two jumps, at which 3 is ineligible.
Thus N_3<=2 N_(>3) on every canonical prefix.
Combining (5),(6) gives the unconditional formal
stopped-count upper bound

    E_P N_J <= 3 sum_(p in P,p>=5) (1/p)
       E_- sum_(r in D_p^ok)
         [1+floor((J-g_r-(p-1))/(2(p-1)))].      (7)

For the full-height successful cohort with
fraction s, the mean number of completed
events is <= the right-hand side divided by s.
A coarser version uses
1+floor((J-(p-1))/(2(p-1))) per affordable pin.
The condition that this sum be log^(o(1)) R
would suffice for the birth compression of
589743f, if a corresponding actual transfer
were available and s were not too small.
No such estimate follows from the finite
bounds here. Indeed in the actual selected
sample below, even using final gain rather
than J, the repeat budget is loose.

## 5. Ordered label entropy: complete decomposition of the outstanding terms

Return to any fixed common-cut cohort (formal
or actual) with physical stationary blocks.
Remove the single birth option as in 589743f.
For each block v let M_p be the mass of
entry label p, B_p=sum_(q<p) M_q.
Writing f(x)=x log x, telescoping gives EXACTLY

    f(sum_p M_p)-sum_p f(M_p)
          = sum_(p>=5) Phi(M_p,B_p).            (8)

In particular no separate p=3 charge is needed.
At each p split M_p=F_p+R_p into first-use
and repeated-p arrivals per root. Split B_p
into B_p^0 (no p used before entry) and B_p^1
(p already used). Because p is ineligible at
its target block, B_p^0 is precisely the
lower-label virgin entry mass of section 2
at every block where M_p>0. For a general
cohort retain only blocks with p-compatible
target positions (a=0 or 2 mod p) in B_p^i.

The function Phi is nonnegative, increasing
in each variable, and subadditive in each
variable separately (concavity and value
zero at the origin of that variable).
Consequently pointwise

    Phi(M_p,B_p) <=
        Phi(F_p,B_p^0)+Phi(F_p,B_p^1)
                       +Phi(R_p,B_p).           (9)

For a normalized root distribution write
alpha_p=E 1{p used}, r_p=E (N_p-1)_+,
b_p^i=(1/N) sum_v B_p^i(v) over compatible
blocks, V_p=(1/N) sum_v Phi(F_p,B_p^0).
Concavity and homogeneity imply

    L_label <= sum_(p>=5) [
         V_p + Phi(alpha_p,b_p^1)
                  + Phi(r_p,b_p^0+b_p^1)].       (10)

Use only matched masses in each Phi for a
tighter bound if they can be estimated.
This treats ALL distinct-label mixing in
the physical blocks, not just an isolated
virgin submix. It avoids treating one
virgin submix for each p as if it were
the exact full entropy contribution.
The remaining within-label time entropy
and the birth entropy are separate.

In a complete formal period, V_p is computed
by the pruned deleted profiles, or bounded
by (3). The other quantities b_p^1 and r_p
are also one-prime tail statistics: enumerate
first-hit pins and follow their continuations,
counting subsequent lower-label entries at
p-compatible blocks and repeated p jumps.
For example b_p^1 <= E[1{p used} times
number of lower-label jumps after first p],
without any product of cross-profile masses.
They may still be large; (10) is not an
asymptotic estimate. For actual selected
cohorts (8)-(10) are exact/upper inequalities
without CRT independence, while the formal
deleted-profile estimates require transfer.

Within-label arrival-time mixing can likewise
be upper bounded by splitting its entry
groups into first and repeated masses:
the two internal time entropies plus
Phi(F_p,R_p) at the block dominate the
original time entropy (refining groups
only increases entropy). The first part
is recoverable from retained pins with
their arrival times recorded; for repeats
use the same-label clock spacing 2p and
height bound from 589743f. This refinement
is a paper deduction, not separately audited.

## 6. Executed audits

All three final scripts executed in the ECMAScript
research runtime, fetched from exact commits and
re-executed with matching output. Reproduce with
node. No separate Node/Lean invocation.

A. research/min_local_negative_first_pin_block_virgin_audit.mjs
commit dab07f61a5cf5969b6fa1f0e6918c1beaf92fb9c
blob 7f417b0ad2aecf9684503a5ef0f9b2fc59399a65

P={3,5,7,11,13}, M=10010, H=16,32,64,
p=5,7,11,13. Tick-based independent full/deleted
simulation, first-pin pruning, exact first-use
block prediction and exact virgin/lower-label
block equality. Counts:
    full roots                       120120
    deleted roots                     15336
    ticks                           5368387
    source tests                      83209
    distinct first pins               36055
    candidate virgin block lifts      72250
    retained virgin block lifts       64477
    full first-use comparisons       120120
    repeated-prime gap checks          7655
    block profile checks              87471
    mass checks                       60920
    entropy checks                       12

At H=64:
 p  raw tests/root  distinct pins/root   first fraction
 5      12.63586          2.59740           .519481
 7       9.16923          2.75175           .393107
11       6.28242          2.85495           .259540
13       5.13506          2.75455           .211888
For p=13 the virgin block mass with births
is .470529 (unpruned .518282);
first/virgin block mixing .185254,
first/virgin LOWER LABEL mixing .100914.
All exact profile comparisons passed.

B. research/min_local_negative_stopped_first_pin_renewal_audit.mjs
commit e3819cf8d98d75a281ac60503a283e2ff3e8d762
blob bdb505a66fdb55371c39907aef3d5d85ca256282

P={3,5,7,11,13,17}, M=170170, p=5,7,11,13,17,
(H,J)=(24,18),(48,30),(64,60).
Event-to-event scan using both candidate waits,
gain stopping, exact activated lift continuations
and full direct replay of every lift.
    full root comparisons           2552550
    deleted roots                     290742
    retained first pins               752253
    affordable                        704473
    unaffordable                       47780
    scanned blocks                    796650
    repeat gain count checks          704473

All assertions passed. At H=64,J=60,p=17
the full stopped mean is 3.370694,
deleted 2.812987, insertion difference
+.557707 (positive contributions .592466,
negative -.034759). Affordable first-p
fraction .153940; actual p mean .158130,
repeat bound using final gain .220297.
Full-height success fraction .954875,
conditional mean 3.023454.
These are fixed-alphabet controls, not
a growing-alphabet event-count estimate.

C. research/min_local_negative_ordered_label_virgin_entropy_audit.mjs
commit de0d68411388e941558a3eb0907162c58e507f98
blob 0960683f24e44c553c75f8507bbb1acf8e09099b

Actual slabs R=12000,48000,192000,480000,1000000,2000000,
K=floor(sqrt R/sqrt(log R)), T=4K,J=floor(T/5).
Selected cohort G_T<=J. Rebuild physical jump
blocks, classify entry histories by prior used
label set, verify (8)-(10), count fresh and
repeated events and repeat budget.
    canonical roots                   622004
    completed full events           14181783
    selected roots                    207261
    occupied jump blocks              389797
    ordered label splits              290701
    compatible target checks           43481
    entropy telescoping checks        389797

At R=2000000, 115899 selected:
mean events 8.050268, distinct labels 4.326810,
repeats 3.723457. p=3 events 2.950276;
p>=5 first uses 3.504560 and repeats 1.595432.
The repeat bound using J and pre-first gains
sums to 47.740377 per selected root; using final
gain instead gives 15.135152. Both are upper
bounds for p>=5 repeats, substantially loose.
Exact label entropy .775514879;
pointwise sum of the three upper terms (9):
    virgin .650460556
    already used .126991058
    repeated .101594954
    total .879046568
Aggregate matched-mass bound (10): 1.319826749.
The three terms are upper charges, not disjoint
percentages of exact entropy. Full final
entropy is 2.621098742, as before.
All assertions passed.

## 7. Remaining task

The first-use/virgin estimates now depend on
distinct pins and whole blocks, not elapsed
tick counts. Exact first-hit renewal separates
fresh activation from repeat tails and retains
negative insertion differences. The ordered
label identity connects the earlier isolated
virgin submix to the entire label entropy.
The major missing bounds are the aggregate
tail costs in (4),(7),(10), in particular
repeated smaller labels, arrival-time entropy,
selected mass at actual near-square-root scale,
and arithmetic transfer of the formal deletion
statistics. No proof of subpower-log mean
event count or coefficient <3, twin infinitude,
or Lean verification. No canonical target,
sibling branch or Context changes.
