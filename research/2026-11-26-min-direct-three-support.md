# Exact three-prime support bounds, with actual MIN clock competition

Continuation of [f239d2e](https://github.com/tara-sooo/A166944-Lean/commit/f239d2e1b38bd0697abbf3aff391f9b965745a8a), on the same independent direct-arithmetic branch. The theorem in that note gives finite L(k) for all k, even odd composite labels, but does not specify a numerical bound for general k. Here the labels are PRIME. We give an elementary reduction for all magnitudes and an exhaustive finite computation for ten small exceptional supports. No cumulative costs, merger estimates, probabilistic distribution, or square-entry hypothesis. Mathematical deductions and exact finite computation, not Lean kernel verification. Twin infinitude remains OPEN.

## 1. Results and notation

Let H be an even horizon, with a relaxed event labelled p an odd prime satisfying H=e mod p, e=+1 or -1, updating H to H+p-1. In actual MIN, e=+1 is the even/minus-neighbor clock n=0 mod 2p; e=-1 is the odd/plus-neighbor clock n=p+2 mod 2p. Select the earliest eligible future tick, then the least label at a tie. Consider arbitrary CONTIGUOUS blocks of nonunit events (quiet ticks omitted), including blocks starting or ending partway through a canonical trajectory.

Write L_R(k) for the optimal universal length over relaxed prime-label paths with <=k distinct labels. Write L_M(k) for the optimal universal length over actual adaptive square-root MIN blocks from canonical odd roots M>=5. The upper bounds below also apply to arbitrary starting plateaus H>=8 and fixed-cutoff MIN with the same ordered prime pool rule. The lower bounds for actual MIN are attained in genuine adaptive canonical paths, even at prime roots.

    k           1     2     3
    L_R(k)      2     6    18
    L_M(k)      2     5    11

L_R(1),L_R(2) proved in the previous note. L_R(3),L_M(3) are exact by the proof plus finite computation below. General explicit L(k) remains unresolved; L_R(4)>=54 is only a previously verified lower bound.

## 2. Two useful repeat identities

The previous two-label result gives:
- on p<q, p>=5, q occurs at most once, and a block has length <=3 (at most p,q,p);
- on {3,q}, q>=7, q occurs at most once, and a block has length <=4 (at most three 3s);
- on {3,5}, a block has at most two 5s and four 3s, length <=6; the largest intervening gain is 16.

For any repeated label r>=5, let G be the gain of all events strictly BETWEEN its two successive occurrences, and e,e' the signs at those occurrences. Necessarily

    G = e'-e+1 mod r,    G even and nonnegative.

For r>=7 this gives G>=r-1 (also true for r=5). Whenever G<3r-1, the only possibilities are

    G = r+delta,    delta=1+e'-e in {-1,1,3}.             (1)

Indeed the residues have odd integer representatives -1,1,3; the multiple of odd r added to these must be odd, and a negative odd multiple cannot yield a nonnegative even number for r>=5.

Now consider three distinct primes p<q<r. Let g be the number of gaps between successive r events in a block with r present (thus g+1 occurrences of r). Each intervening gap uses only p,q. In all cases above its gain is <3r-1: for p>=5 it is <=2p+q-3, for p=3,q>=7 it is <=q+5, and for p=3,q=5 it is <=16 with r>=7. Thus (1) applies throughout. Let B_j be the horizon just AFTER the j-th r event, e_j its sign, and T_j=B_j-e_j. Across every internal gap,

    B_(j+1)-B_j = 2r + e_(j+1)-e_j,
    T_(j+1)-T_j = 2r.                                  (2)

The adjusted horizons T_j form an exact arithmetic progression, even if signs change. Any boundary suffix containing q must satisfy the same q-congruence restriction as an internal gap.

## 3. All p>=5: a universal bound 11, except two explicitly finite supports

If r occurs once, length <=7. Otherwise every internal gap must contain q and at least one p: neither p nor q alone contributes r-1. The only possible words and gains are

    A: pq or qp, G_A=p+q-2;
    B: pqp,      G_B=2p+q-3.

Here G_B-G_A=p-1. Since delta ranges only over {-1,1,3}, both types cannot occur unless p=5 and r=q+4. First treat a single possible type. Its delta is fixed. If delta=-1 or +3 then its sign transition cannot be repeated, so g<=1 and total length <=2+3+3+3=11. It remains to consider delta=1, so all r signs equal and B_j is a progression of step 2r.

### A, delta=1

Now r=p+q-3. Each gap contains q at offset 0 or p-1 from B_j. The q-activation condition says B_j mod q belongs to {+1,-1,2-p,-p}. After shifting all residues by p, the allowed representatives are

    E={0,2,p-1,p+1} subset [0,p+1], all even.

Since p+1<q, their representatives are distinct and unique. A consecutive pair of progression values in E has ordinary difference congruent to d=2(p-3) mod q. Both this difference and d are even, so the difference minus d is an EVEN multiple of q. Its lower bound is -3p+5>-3q, and upper bound is 7-p<q. Therefore the difference must be d or d-2q.

For p>=11, d>p+1, so only d-2q is possible; it is <=-10, and must move from the upper cluster {p-1,p+1} to the lower cluster {0,2}. Two such consecutive differences are impossible. For p=5 or 7, d-2q is outside the range of differences and 2d>p+1, so again two consecutive differences are impossible. Thus there are at most TWO consecutive progression values in E, i.e. g<=2. If g=2 and the suffix after the last r contained q, B_3 would also belong to the same residue set, impossible. That suffix has length <=1. Consequently the length is at most 3+2*2+3+1=11. For g<=1 the result is even smaller.

### B, delta=1

Here r=2p+q-4. Suppose g>=2. Within each pqp gap, comparing the two p pre-horizons forces q=2 or 4 mod p: in fact q-2=e'_p-e_p mod p; q=0 mod p is impossible. Across two such gaps their first p pre-horizons differ by 2r=2(q-4) mod p. If q=2 mod p, this difference is -4, which is not 0,+2,-2 modulo any prime p>=5. So q=4 mod p. The q pre-horizons in consecutive pqp gaps also differ by 2r mod q; since q does not divide r this must be +/-2 mod q. Hence q divides 2p-3 or 2p-5. As q>p, either equality q=2p-3 or q=2p-5 holds. The condition q=4 mod p then requires p=7 or 9; p=9 is not prime, and p=7,q=11 would give r=21, not prime. Contradiction. Thus g<=1 and length<=11.

### Both types (p=5,r=q+4)

The two types have respectively delta=-1 and +3, and must alternate if both occur. Here T_j from (2) at each gap has q-residue in {-6,-4,-2,0,2}: its q offset is 0 or 4, and e_q-e_j is -2,0,2. Its step modulo q is 8. For q>16, the representatives in [-6,2] cannot wrap on this step, so g<=2. If g=2, the representatives must be -6,2. The first requires e_1=+1; the second requires e_2=-1 and q at offset 0. But e_2=-1 requires the B gap pqp (delta=+3), in which q is at offset 4. Impossible. Thus g<=1. The only prime exceptional supports for q<=16 are {5,7,11},{5,13,17}, handled by finite computation below.

We have proved the common upper bound 11 for every nonexceptional support without 3, even without clocks.

## 4. p=3, q>=7: relaxed bound 12 and actual bound 11, except four finite supports

Again if r occurs once, length <=9. Every internal gap must contain one q and j of the label 3 with 0<=j<=3 (without q the gain <=4). Thus G=q-1+2j, and (1) implies

    d=r-q in {2,4,6},  delta=2j-d-1.

The q offset in any lower block is 0,2,4 because no run of 3 exceeds two. Therefore T_j mod q, for every internal gap or suffix containing q, belongs to

    E={-6,-4,-2,0,2}.

Its step modulo q is 2d. For q>2d+8 the representatives cannot wrap, so at most floor(8/(2d))+1 consecutive representatives in E are possible. Also define f(H)=H mod 3 in {0,1,2}. Every label-3 event decreases f by 1; a prime 1 mod3 leaves it unchanged, and a prime 2 mod3 increases it by at most 1. Telescoping this elementary bounded residue gives the total number of 3s <=2 + the count of labels 2 mod3. This is just a three-state identity, not an asymptotic cost assumption.

### d=2, q>12

Here q=2 mod3, r=1 mod3, so #3 <=2+#q. We have g<=3. If g<=1, #r<=2,#q<=3, length<=10. If g=2 and the suffix contains q, T_1,T_2,T_3 must have representatives -6,-2,2. The first -6 means e_1=+1, q has sign -1 and is preceded by two 3s. If the prefix contained q, the gain between that prefix q and this first internal q would be at least (r-1)+4=q+5 and at most q+9 (at most two further 3s in the prefix). This is <3q-1 and violates (1) applied to q. Therefore the prefix cannot contain q. If the suffix does not contain q, the same count bound follows immediately. Hence for g=2, #q<=3,#r=3, length<=11.

For g=3 the three representatives must again be -6,-2,2. The first gap begins with two 3s, so a prefix q is impossible by the preceding repeat argument. At T_3=2 the sign e_3=-1 and q is at offset 0 with sign +1. Its gap must contain >=2 label-3 events since delta=1 or 3, and at most two since they all follow q consecutively. Thus it contains exactly two. A suffix q is impossible by the same repeat-gain argument q+5..q+9. Consequently #q=3,#r=4,#3<=5, giving relaxed length<=12.

For ACTUAL MIN, this g=3 configuration is impossible. The first gap has exactly the word 3,3,q (e_1=+1 and two leading 3s force delta=1, j=2); q_1 is odd-side and the next r_2 is even-side. Immediately after q_1 the horizon is 1 mod3: the double 3 reduced residue 2 to 0, then q added 1. Since r=1 mod3, r_2 preserves residue 1. In particular an even 3-clock is available within 6 ticks after q_1 and stays available through r_2 unless a 3 event occurs.

T_2=-2 and e_2=+1 imply B_2=-1 mod q. Since e_3=-1, the second gap has delta=-1, j=1; its word is either q,3 or 3,q. In the q,3 case q_2 is odd-side, same as q_1. But two same-side q hits are at least 2q>6 ticks apart, and the available 3 clock must preempt the proposed sequence q_1,r_2,q_2. In the 3,q case q_2 is even-side (B_2+2=1 mod q); the preceding 3 reduced residue 1 to 0, then q again changed it to 1. The next r_3 preserves this residue, and q_3 must be even-side (T_3=2). The identical 3-clock obstruction now prevents q_2,r_3,q_3. Thus actual g<=2 and length<=11. The finite exception for q<=12 in this case is {3,11,13}.

### d=4, q>16

Here q=1 mod3,r=2 mod3, and g<=2 from the representative step 8. In fact q occurs at most twice: successive q occurrences straddle exactly one r and at most four 3s, so their intervening gain is q+3+2j, 0<=j<=4, strictly below 3q-1. By (1) for q this is possible only with j=0 and delta=+3 (sign change -1 to +1), which cannot recur on the next pair. Hence #q<=2,#r<=3,#3<=2+#r, giving length<=10 even in the relaxed model. Exceptions for q<=16: {3,7,11},{3,13,17}.

### d=6

The gap gain <=q+5=r-1, so delta=-1 and g<=1. For q>=11, repeated q would have intervening gain q+5+2j (0<=j<=4), strictly below 3q-1 but above q+3, impossible. Thus #q<=1,#r<=2,#3<=2+#q+#r, length<=8. Exception: {3,7,13}.

This proves both claimed nonexceptional bounds without an asymptotic hypothesis.

## 5. p=3,q=5 and the forced doublet; exact actual L_M(2)

If a 3 event is on the odd side, its tick is n=5 mod6. Its horizon changes from 2 mod3 to 1 mod3, so at n+1 the even 3 clock is eligible and wins (smallest odd prime). Thus in EVERY actual path the next nonunit event is 3 at the next tick. This is valid for both adaptive and fixed pools containing 3. A block is allowed to end before the forced successor, but cannot insert a different event between the pair.

From the earlier exact two-label proof, the only length-six pattern for {3,5} is 3,5,3,3,5,3: the first 5 must have sign +1 and the second -1, with two middle 3s, and the initial 3 changes the residue modulo 3 from 2 to 1 to prepare the first 5. The initial 3 is therefore odd-side, and its forced successor is not 5. So actual length-six is impossible. Other two-label supports have relaxed upper <=4. Hence L_M(2)<=5. Equality is witnessed below from prime root M=569.

For {3,5,r}, r>=19, the smaller-label gain <=16 is <r-1, so r cannot repeat and relaxed length<=2*6+1=13. Actual length<=2*5+1=11. Remaining supports {3,5,7},{3,5,11},{3,5,13},{3,5,17} are finite.

## 6. Complete finite computation for ten remaining supports

The above reductions cover ALL primes of arbitrary magnitude except the ten listed supports. The following exact dynamic programs are finite certificates, not samples of starting horizons.

For each S=(p_1,...,p_k), Q=product S, use the relaxed period H=2j, 0<=j<Q. Each allowed event maps j to J=j+(p-1)/2<=Q, by the fixed-set barrier at 2Q. Its congruence is periodic in j with period Q. Compute longest relaxed paths by backward recurrence in j, endpoint j=Q length 0. Translating the period to sufficiently large positive horizons preserves relaxed labels.

For actual clock competition also use time phase tau=t mod 2Q. At each plateau let m be the number of enabled labels in the INITIAL SEGMENT of ordered S, with 1<=m<=k. We intentionally relax the adaptive threshold: allow this number to increase arbitrarily from plateau to plateau, rather than require the exact square-root cutoff. True adaptive eligibility is monotone and true fixed-cutoff eligibility is constant; every actual block with labels in S therefore has such an enabled-count history. Starting with m=1 gives an upper bound for all possible initial enabled prefixes. Enabling zero labels cannot start a nonunit event in the block. Other primes outside S may cause an earlier or tied smaller event; they can only end the S-block or leave its next event unchanged. If the actual next label is in S, it must equal the earliest/least selected among enabled S.

Let D(j,tau,m) be the maximum length of this relaxed-clock block with minimum enabled count m. For each e>=m, compute the deterministic earliest/least next event (p,w) among the first e labels using H=2j and t=tau. If none is eligible, this option stops. Otherwise its successor has j'=j+(p-1)/2>j, tau'=(tau+w) mod 2Q, minimum enabled count e. The exact recurrence is

    D(j,tau,m)=max(0, max_(e>=m with hit) [1+D(j',tau',e)]).

Endpoint D(Q,*,*)=0. Thus descending j computes ALL residue/time/prefix states, even those not reachable from canonical sources. A true S-block cannot cross the barrier; its length is bounded by the maximum of D. This is an upper computation in a clock model broader than actual MIN, not a simulation of a selected initial root. No assumption about prime distribution is used.

| S | exact relaxed maximum | relaxed-clock maximum (monotone enabled prefix) |
|---|---:|---:|
|3,5,7|14|9|
|3,5,11|12|10|
|3,5,13|8|7|
|3,5,17|18|11|
|3,11,13|12|9|
|3,7,11|8|7|
|3,13,17|8|7|
|3,7,13|4|4|
|5,7,11|5|5|
|5,13,17|6|6|

Together with sections 3-5 this proves L_R(3)<=18 and L_M(3)<=11. The relaxed word

    3,5,3,3,5,17,3,5,3,3,5,3,17,5,3,3,5,3

from H=344 to420 uses {3,5,17} and attains 18. All selected labels also satisfy adaptive square-root eligibility in this relaxed example; the clock order is NOT asserted. The actual witness below attains 11. Therefore both universal bounds are optimal. The entire proof is a mathematical case reduction plus exhaustive exact finite computation, not a Lean proof.

## 7. Independent checks and actual prime-root witnesses

[Audit at 450adea](https://github.com/tara-sooo/A166944-Lean/blob/450adeadb208820f12976aa1e11af39a2e5f47c5/research/min_direct_three_support_audit.mjs), blob cc39d23f350a981b6e84ae9ab6a7122ee092db79, exact remote readback. Run from repository root:

    node research/min_direct_three_support_audit.mjs 100000 100

Executed the actual ECMAScript audit function in the tool runtime, not a separate Node process. The ten finite clock DAGs include 13,572,300 nonterminal phase/prefix states and 68,910 independent restricted literal tick comparisons. The exact clock maxima agree also when all S labels are enabled throughout. Additional tests: 560 triples from primes3..59, nonexceptional relaxed maximum12 and nonexceptional no-3 maximum9 in that range; 3760 direct three-term progression tests in the A/delta1 residue set for p<=300,q<=500 with r prime. All assertions passed. These extra tests are diagnostic, not the general proof.

Scan all odd M=5..100000 for at most 100 nonunit events each (or earlier stop): 1,011,080 actual event incidences, no range truncation, 35,999 odd-side 3 events independently checked for the forced next 3. The maximum observed contiguous lengths using <=1,2,3 distinct labels were respectively 2,5,11; same maxima for prime roots. All equality witnesses are replayed from their canonical root with literal parity-GCD ticks.

- M=5, events 3,3 at n=11,12.
- PRIME M=569, block start (t,H)=(578,1156): labels 5,3,3,5,3 at n=580,581,582,587,588, ending H1170.
- PRIME M=7949, block start (8167,16186): labels 5,3,3,5,3,17,5,3,3,5,3 at n=8170,8171,8172,8177,8178,8179,8180,8183,8184,8187,8190, ending H16230.
- Additional all-odd witness M7191, starting block at (7208,14416): 5,3,3,5,3,47,5,3,3,5,3, ends H14490.

These actual witnesses, not merely relaxed-clock examples, prove the lower bounds for L_M(k). No Lean/lake executable was available; no Lean files changed. No external novelty claim.

## 8. Direct global consequence and next problem

Under finite twin primes, every adaptive MIN trajectory starting above the last twin center is infinite. Combining the exact clock bounds with that fact, EVERY block of 6 nonunit events must use >=3 distinct primes, and EVERY block of 12 must use >=4 distinct primes. These statements are uniform over arbitrarily large sources and all block starting positions. In the earlier spatial formulation one may now take m=12 for four distinct selected labels: for every even X at or above the initial horizon, at least four distinct primes are selected in the horizon interval

    [X, X+13*sqrt(X+1)+169/4].

This follows from the overshoot and sqrt(H'+1)<=sqrt(H+1)+1/2 inequality. It is not a statement about the ordinary density of primes in intervals and it does not yet contradict finite twins.

The exact three-label analysis suggests a new direct way to force a twin witness: if a block on {3,q,r}, q>12, has at least three intervening r gaps with q in each and the relaxed residue geometry d=2, then actual clocks rule it out, while d=4,6 have shorter restrictions. The more general necessary statement is the exact 12-event/four-label constraint. What remains missing is an arithmetic reason that, at arbitrarily large actual roots, a block must exhaust all its available transitions without reaching four distinct labels. Finite CRT translation alone cannot supply an absolute-size bound, as earlier notes show. No unbounded stopping-root family, finite-twins contradiction, or original A166944 record conjecture proved. Next independent target: generalize the adjusted-horizon arithmetic progression (2) and finite support clock compression, perhaps by controlling how new labels enter rather than enumerating ever larger supports. Main and sibling branches untouched.
