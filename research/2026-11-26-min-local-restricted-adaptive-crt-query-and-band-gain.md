# Adaptive CRT queries and band gain on actual mixed restricted trajectories

2026-11-26 JST. Continuation of 26166e773aacca007c21663c367655e16367557e.
Use a deferred residue query identity to transfer height occupation to
the number of distinct used labels on the actual enlarged trajectory,
not just to the first preemption of an old trajectory. Exact finite
probability law, deterministic repeat spacing, conditional band-gain
bound, executed finite diagnostic. No Lean verification, external
novelty claim, or twin-infinitude proof.

## 1. Actual restricted trajectory as an adaptive residue query process

Let A be a finite set of odd primes containing 3 and with maximum
label z. Start canonical roots X=0 mod6, v0=X/2+3, uniformly over
the full seed period P=4 product_(r in A) r. For a finite displacement
cutoff D>0 stop at first terminal or first arrival with gain >=D,
including that last event. The arguments on first use also hold
without displacement truncation by the primorial wall.

Write G=u-X, W=v-v0 at a source. The half-deficit h=v-u/2
is 3+W-G/2. At a tick n=v+j the parity is determined by X mod4
and the relative transcript. For e=+1 at even n, e=-1 at odd n,
eligibility for an odd prime p requires

    p | 2(h+j)+1  (even),
    p | 2(h+j)-5  (odd),

respectively, and the remaining condition is

    X = e-G mod p.                                (1)

This is equivalent to the original clock congruences, not a
weakened eligibility condition. The two defect forms are odd
and nonzero. The root period provides uniform independent
residues X mod p for p>=5 conditional on X mod12.

One can run the exact restricted map by examining ticks in order
up to 2z from each source, querying the primes dividing the
appropriate defect in increasing order. At a candidate prime p,
test (1); the first positive query selects the event. No further
queries at that tick are necessary. If there is no positive
query within 2z, there is no eligible clock, hence the source is
a terminal. This terminal scan does not add any actual time or
gain to the trajectory. It is only a finite method of identifying
termination. Repeated negative queries can be cached, and after
the first positive query to p its residue is known. The process
does not reveal the whole prime factorization of the source in
advance.

For p>=5 admitted, let I_p indicate at least one selection of p
before the stated stop, and Q_p count the distinct residues
queried at p up to and including its first positive query, or
all those queried if no positive query occurs. No queries after
first use are counted. This is an information count on actual
trajectories, not a count of all clock opportunities.

## 2. Exact conditional rank identity

Fix X modulo P/p. This fixes all other prime residues and the
parity of the canonical time. Only the p-residue remains uniform.
Run the same algorithm with every query to p answered negatively.
This is exactly the p-deleted trajectory, with the potential
p-queries recorded, and with the same displacement stopping rule.
Let q in [0,p] be the number of distinct p-residues queried on
this negative branch, in first-occurrence order. It is well-defined
even if no actual lift avoids them all.

For the actual residue equal to the i-th recorded class, the
first i queries follow precisely that negative branch until query
i is positive. The p-event then occurs, and Q_p=i. For each of
the p-q remaining residues, the whole branch is followed and
Q_p=q, I_p=0. Future events after a positive answer do not affect
these counts. Thus, conditionally on X modulo P/p,

    Pr(I_p=1) = q/p,
    E Q_p = [q(q+1)/2+(p-q)q]/p
          = q-q(q-1)/(2p).                         (2)

In particular

    E Q_p/p <= E I_p <= 2 E Q_p/(p+1).             (3)

Both inequalities survive averaging over the fixed other
residues. They need neither independent event choices nor
a small old-relay cap. The factor 2 can be replaced by
1/(1-(q-1)/(2p)) conditionally, when q>0.
The identity handles all prime orderings, including p
smaller than other admitted labels, because the query
algorithm checks candidates in the same least-prime order
as the original tie rule.

For any fixed nonnegative label weights c_p, summing (3) gives

    sum_p c_p E Q_p/p
        <= E sum_p c_p I_p
        <= sum_p 2 c_p E Q_p/(p+1).                 (4)

This is a two-sided expectation relation for DISTINCT label
usage; it does not count repeated selections of a known p.
It also applies to any deterministic stopping rule defined
from the revealed transcript, provided it can be run on the
negative branch and does not inspect unknown residues.
Here we use only the stated physical displacement stop.

## 3. Actual mixed-trajectory occupation bounds the query cost

Take y>=7, maximum label z<=2y and a band B of admitted
primes in [y,2y]. We may take all primes <=2y in A; there
is no frozen old transcript. Define a_y, Phi_y and down
local times D_y(h) from 26166e7 using this band and the
ACTUAL mixed trajectory up to its stop. Put

    K_B=sum_(p in B) I_p,
    C_B=sum_(p in B) Q_p/p.

Every queried p-residue during an actual event wait is
counted by the appropriate defect in (1). We may upper
bound by both parities and include the firing tick.
At the possible terminal scan, at most two distinct
residues per p can be queried: the offset u is fixed
throughout the scan and only the sign e varies.
Consequently, pointwise on actual paths,

    C_B <= 2 sum_(p in B)1/p
             + Phi_y(h_end)-Phi_y(3)
             + sum_h a_y(h) D_y(h).                 (5)

The last two terms are the exact coarea sum over all
actual upward ticks (including firing). This holds even
when a band label has already fired and substantially
changed the subsequent trajectory. Counting its later
opportunities only enlarges the upper bound.

Combining (4) with (5) gives the unconditional full-period
inequality

    E K_B <= 2 E C_B
      <= 4 sum_(p in B)1/p
         + 2 E[Phi_y(h_end)-Phi_y(3)+sum_h a_y(h)D_y(h)].

Unlike 7021cc1 and 26166e7, this is not the activation
probability in CRT lifts of an old trajectory. The
expectation is over the actual system with all labels
in A present, and K_B counts every distinct band label
used, not just the first one.

## 4. From distinct labels to all band gain

For any admitted p>=5, two successive selections of p
in its own subsequence have even source offsets
congruent to +1 or -1 mod p. The difference is at least
p-1 by strict increase and the previous p-gain.
The possible positive even differences are 0,+2,-2 mod
2p. Since p>=5, the smallest such difference at least
p-1 is 2p-2. Equivalently the intervening gain from all
other labels is at least p-1. This does not require those
other labels to be smaller than p.

If total gain G is at most (C+2)y, the number of
occurrences of any p>=y is therefore at most

    1+floor(G/(2(p-1))) = O_C(1).

Take the displacement stop D=ceil(C y), C>=1 fixed.
All event labels <=2y, so the final overshoot is <2y
and G<= (C+2)y+1. The total time of actual waits is
<=3G; hence Hmax<=3+3G=O_C(y).
Let G_B be the sum of ALL gains from band labels up
to this stop, and L_y=sum_(h>=ceil((y-1)/2)) D_y(h)^2.
Then pointwise G_B<=O_C(y) K_B. Use (5), the bound
sum_(h<=Hmax) a_y(h)^2=O_C(1/(y log y)) from 26166e7,
and Cauchy-Schwarz, followed by Jensen's inequality:

    E K_B <<_C 1/log y + sqrt(E L_y/(y log y)),
    E G_B <<_C y/log y + sqrt(y E L_y/log y).        (6)

This includes the entire stopped actual trajectory.
In particular, if its mean high-height occupation
energy is o(y log y), then its expected total band
gain is o(y). Since the possible gain overshoot is
included, this also bounds band contributions on
crossings of displacement C y that do not terminate.

There is a probability version without a mean energy
assumption. On this stopped ensemble K_B<=G/(y-1)=O_C(1).
If L_y/(y log y)->0 in probability, apply the bounded
conditional estimate (5) carefully as follows: C_B itself
need not be uniformly bounded by that vanishing expression
on exceptional roots. Instead use the exact conditional
rank law and Markov to control first hits with few queries.
For each p, if I_p=1 and Q_p<=m, the conditional number of
such lifts is min(q,m), hence probability <=m/p.
More generally truncate the entire adaptive scan when the
weighted sum of distinct queries C_B would exceed a fixed
epsilon. This is a transcript stopping rule: the new
query is determined before its answer and can be omitted.
Then C_B<=epsilon for the truncated process, and by (3)
Pr(any positive band query before that stop)<=2epsilon.
On any original path with C_B<=epsilon, the truncation
does not intervene. Thus

    Pr(K_B>0) <= Pr(C_B>epsilon)+2epsilon.          (7)

The stop for this auxiliary process must occur BEFORE
the query that would cross epsilon; otherwise one has
to account for that extra query. Query counters cease
for a prime after its first positive answer as usual.
The no-hit branch for each p is still deterministic.
By (5), the energy and height assumptions make C_B->0
in probability. Use (7), then K_B bounded and G_B/y
bounded, to obtain E G_B=o(y). This argument avoids
assuming uniform integrability of C_B. It supplies a
probabilistic form of the occupation criterion on the
actual enlarged trajectory.

## 5. Identify precisely the lower labels responsible for the energy

For fixed eta>0 split the actual down-local-time into
D_large from labels >=eta y and D_small from labels
<eta y. At the above displacement stop, there are at
most O_(C,eta)(1) large events. Their total interval
length is <=G/2, so

    sum_h D_large(h)^2 <= O_(C,eta)(y).

By the triangle inequality in l2 on the high region,

    sqrt(L_y) <= sqrt(sum_(h>=h0) D_small(h)^2)
                                      + O_(C,eta)(sqrt y).

Thus the macroscopic labels themselves cannot cause
an occupation energy of order y log y. Only overlapping
down intervals of smaller labels need to be estimated
for the criterion in (6)-(7). This statement is about
actual stopped mixed paths, not old paths conditioned
to avoid the high labels.

There is also a first-moment version: for fixed integer
z0>=3 let S_z0 be the total length of down intervals of
labels <=z0 lying at h>=h0. The translated-interval
prime upper bound in 7021cc1 and 26166e7 gives

    C_B <<_C 1/log y + 1/log(2+z0) + S_z0/y.

Consequently (4) and repeat spacing imply

    E G_B / y <<_C 1/log y + 1/log(2+z0)
                                      + E S_z0/y.   (8)

In particular vanishing high-height gain fraction of
every fixed small alphabet suffices to show negligible
actual band gain. This is an expectation inequality
on the entire stopped path, not a comparison with
the deleted path up to its first band event.
It still needs a bound on S_z0; the arbitrary-phase
small-run caps alone do not give this bound.

## 6. Executed finite diagnostic

Source research/min_local_restricted_adaptive_crt_query_audit.mjs,
commit 4a5aca63ebf093459bf6ca8c853cf8955195724e,
blob a686fa195bb8970319271e9c648f6242e984b92f.
Reproduce: node research/min_local_restricted_adaptive_crt_query_audit.mjs.
Executed as ECMAScript in research runtime, fetched at exact commit,
and re-executed with identical output. No separate Node or Lean process.

Four full periods, inclusive max label z=7,11,13,17,
band lower cutoff y=5,6,7,9 respectively and D=4y.
Three separate actual local samples at y=127,503,997,
z=2y, D=4y, each of 2,000 roots. Local slabs are
[100000,112000) for y=127 and [1000000,1012000)
for y=503,997. The local rows test only pointwise
relations; they are NOT treated as full-period
probabilities or tests of (2)-(4).

At every source independently compute the true
next event using neighbor factors, then enumerate
all eligible defect queries up to that tick (respecting
least-prime priority), or the finite terminal scan.
Check that all positive unknown-prime queries exactly
select the true event. Cache distinct negative residues
and record first positives. Sum integer query counts and
hits separately in EVERY conditional p-lift group of
each full period. If a group has q hits, its sum of
query counts must equal p*q-q*(q-1)/2, the integer
form of (2). Also check the pointwise coarea charge
and repeated-label spacing.

    kind     y    z   roots   distinct band uses   all band events   mean band gain
    period   5    7      70             56                 68          4.7143
    period   6   11     770            456                507          4.8961
    period   7   13   10010           8291               9047          7.6613
    period   9   17  170170         103292             105983          7.5269
    local  127  254    2000           1121               1121        102.8310
    local  503 1006    2000            665                665        251.7010
    local  997 1994    2000            113                113         66.1890

Totals: 187020 root/cutoff incidences, 669735 actual
events, 117504 band event incidences, 113994 first
uses, 3510 repeat spacing checks, 2362216 distinct
queries, 6105279 actual ticks and 16910430 virtual
terminal ticks. All 41884 complete conditional
lift-group rank identities and 187020 pointwise
coarea query bounds passed. Counts overlap across
cutoffs and shared trajectories. The probability
stopping inequality (7) and asymptotic estimates
(6),(8) are mathematical deductions, not tested
as asymptotic rates by this script.
For local y=997 the sum of weighted query costs
is 409.25265, while distinct band uses total only
113. This is a concrete example of why the lower
expectation inequality in (3) cannot simply be
applied to empirical short-interval averages.

## 7. Remaining connection to termination

The previous occupation approach only bounded the
probability of a first new-label selection while
following an old trajectory. The rank identity now
controls all distinct uses and, via spacing, all
band gain of the stopped mixed trajectory. The
energy contribution of macroscopic labels is O(y).
However the small-label activity at high height
is still uncontrolled. Even showing negligible
gain in one top band does not force the full
trajectory to terminate: lower labels can carry
the remaining displacement. A multi-scale argument
needs control of that lower transport without
reintroducing the old period/phase-concentration
problem. Full-period expectations do not transfer
to intervals of length O(y^2) by this identity.

No proof of the required restricted terminal
displacement in physical slabs, no twin-infinitude
proof, no changes to canonical Lean targets or
sibling branches.
