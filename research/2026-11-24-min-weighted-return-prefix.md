# Canonical MIN: exact deleted-prime return, 2P prefix, and weighted late one-donor returns

2026-11-24 JST. Research-only continuation of PR #9 at ec7a13cf5b000551efa3ab03cb55dd8683de0880. The following are paper deductions from the existing canonical MIN clock and LOW7 barrier, not new Lean-checked theorems. The aggregate contraction and twin-prime conjecture remain OPEN.

## 1. Exact MIN leave-p-out return

Use the actual odd canonical sources M in [X,2X), X dyadic and divisible by 4, start (M+2,2M-2), stop K(M)=floor((7M-1)/4), B=ceil(sqrt(7X)). The MIN choice is lexicographically earliest (time,prime) among eligible clocks; C increases by p-1 when prime p is selected.

From any genuine post-p state, delete p from the eligible pool and run the shadow with the SAME K(M). At a shadow plateau, let h be the least (time,label) candidate of all other primes; let h_p be the next p clock if p divides C-1 or C+1. Missing candidates are infinity. The next true p selection is exactly the first plateau with h_p < h and h_p.time <= K(M). Otherwise the shadow makes the identical next non-p update, or terminates. Induction proves both existence and nonexistence equivalence. A time tie is won by p only if its label is smaller; the GCD-wheel weak-time comparison is NOT interchangeable with the MIN comparison.

If p>=5, sigma_0 and sigma_1 in {-1,+1} are the two signs of C+sigma at consecutive p selections, and E is the total p-free gain between them, then p divides (p-1)+E+sigma_1-sigma_0. This is positive and even, so

    E=(2j-1)p+1+sigma_0-sigma_1, j>=1.

This gives a target lattice in donor gain, not just the short recharge bound E>=p-1. The shadow needs both this congruence and the chronological winner check.

Define T_k(X)=#{(M,p): p>y, N_p(M)>=k} in the full canonical MIN word, counting ORIGINAL source tags. Then H=sum_k T_k. For some fixed rho<1/2, a contraction T_(2k)<=rho T_k for k=k0*2^j, k0=ceil(sqrt(log B)), on an unbounded sequence of windows suffices: H<=k0*T_1[1+1/(1-2rho)]=O(XB/sqrt(log B)). If no twin terminal exists the known clock bound with L<=sqrt B and summed horizon gives H>=(9/224-o(1))*XB. The contraction remains OPEN. The shadow equality alone is not a mixing theorem; source mass is not an independent distribution on CRT residues.

## 2. Shorter full 2P prefix with fixed LOW7

Fix y=7 and L=210; P=pi(B)-4. Let v_M be the first min(2P,|HIGH7 word|) HIGH7 labels, without subsampling. Define D=sum_M (|v_M|-#distinct v_M). The existing clock_budget in canonical_min_prefix.lean gives

    non-twin terminal => K(M)-(M+2) <= (|HIGH7 word|+1)*(2B+630).

For 2P*(2B+630)<3X/4-2 (eventually true since P~B/log B), every non-twin source has >=2P high selections. Hence D >= XP/2 if all sources are non-twin. Thus D < XP/2 on unbounded sufficiently large dyadic windows suffices. This finite implication uses only the existing clock theorem plus the pigeonhole principle; the new unsampled variant has NOT been compiled in Lean.

## 3. NEW: all-position source-weighted one-donor theorem in the short prefix

Let Q>=840 and Q<=B. Count R_1(X,Q), the number of consecutive occurrences of the same selected prime p>=Q in v_M which have precisely one HIGH7 selection q between them. All low selections between the three highs are permitted. Count each return in each ORIGINAL source, not distinct reset states. The first p may be at ANY position in the prefix.

**Claim.** For any fixed 0<alpha<1/2, take Q=ceil(B/(log B)^alpha). Then

    R_1(X,Q) = O(X B (log B)^(2alpha-2)) = o(XP).

Proof. Write C for the horizon immediately BEFORE the earlier p, and E_1,E_2 for the gains of the two LOW7-only blocks in p,q,p. Each E_i is even and 0<=E_i<210 by the existing even-multiple barrier; hence E_1+E_2<=416. The PR #8 recharge bound shows q>=p-416>=p/2. Consecutiveness of the p occurrences gives q!=p. The endpoint divisibilities show

    q = 2 + sigma_0 - sigma_2 - E_1 - E_2 (mod p).

There are at most 3*209=627 residue classes for q modulo p, so at most 627*(floor(B/p)+1) candidate integers q (overcounting composite labels is harmless).

For each distinct prime pair p,q, the FIRST TWO divisibilities hold at the possibly late state C:

    p | C+sigma_0,
    q | C+(p-1)+E_1+sigma_1.

Fix E_1 and signs sigma_0,sigma_1. The CRT fixes one residue class of C modulo pq. Since initial C>=2X and the existing invariant C<=2t<=2K(M)<7X bounds all actual event states, each class contains at most 5X/(pq)+1 candidate C values. There are at most 105*4=420 choices of E_1 and signs. Thus the number S_Q of possible pairs (C,p) at the first endpoint of such a return satisfies

    S_Q <= 420*627 * sum_{Q<=p<=B prime} (floor(B/p)+1)*(10X/p^2+1).

By prime counting and partial summation, for Q=B/(log B)^alpha up to rounding,

    sum_{p>=Q} p^-2 = O(1/(Q log Q)),
    sum_{p>=Q} p^-3 = O(1/(Q^2 log Q)),
    sum_{Q<=p<=B} 1/p <= pi(B)/Q.

Since X=Theta(B^2), S_Q=O(B(log B)^(2alpha-1)). These are bounds on STATE LABELS, not source counts yet.

The crucial source-weight step: before ANY high event in the first 2P highs, total gain from the canonical initial C_0=2M-2 is at most G=2P(B+210), because there are at most 2P preceding low blocks, each gain<210, and at most 2P preceding high gains, each <B. For a fixed C, all source origins therefore have C-G<=2M-2<=C. Initial C_0 values of odd M are spaced by 4, so at most floor(G/4)+1 sources can visit the fixed pair (C,p), even after arbitrary coalescence. Each source visits C at most once because each event strictly increases C. Consequently

    R_1(X,Q) <= (floor(G/4)+1)*S_Q
             = O(X B (log B)^(2alpha-2)),

which is o(XP) for alpha<1/2. This extends the initial p,q,p source-count result to ALL POSITIONS in a bounded prefix. It does not assert a uniform bound for unrestricted full trajectories. In particular alpha=1/3 yields O(XB/(log B)^(4/3)).

For p>=Q>=840 there cannot be a return with zero HIGH7 donors, since LOW7 gain <210 <p-1. Thus the entire large-label repeat count is R_1 + R_>=2, where the latter counts consecutive p returns with at least two intermediate high selections (not necessarily distinct). This avoids counting all pairs of nonconsecutive occurrences.

## 4. Remaining sufficient conditions

Choose Q=ceil(B/(log B)^(1/3)), a=ceil((log B)^(1/6)), n(M,p)=multiplicity in v_M. Set

    A(X)=sum_{M,7<p<Q prime} (n(M,p)-1-a)_+
    R_>=2(X)=#large-prime consecutive returns with >=2 high donors.

For all sufficiently large windows,
    D <= (X/2)*pi(Q)*a + A + R_1 + R_>=2
      <= A + R_>=2 + o(XP).

Therefore the single OPEN condition

    liminf_(dyadic X) (A(X)+R_>=2(X))/(XP) < 1/2

suffices for infinitely many twin primes. Stronger separate estimates A=o(XP), R_>=2=o(XP) also suffice on the same windows. The small-label base is O(XP/(log B)^(1/6)). A sufficient small-label-only approach is aggregate tail contraction with fixed rho<1/2 starting at k0=a+1: the contribution above k0 is O(k0 * X pi(Q))=o(XP). This does not prove that contraction.

The one-donor result uses a fixed LOW7, NOT a growing low cutoff. For two or more donors the CRT modulus includes more labels; naive summation of the +1 remainder over histories is too expensive. The missing source-weighted control is now specifically small-label excess and large-label multi-donor returns. Further reduction or genuine arithmetic cancellation is needed.

## 5. Reproducible audit

    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_weighted_return_audit.cpp -o /tmp/min_weighted_return_audit
    /tmp/min_weighted_return_audit 256 1024 4096 16384 65536 262144 1048576 4194304

The C++ audit counts all actual sources up to their own K(M); compares every clock decision at X=256,1024 against literal parity-GCD scanning (6140 checks); and checks next p choices against deleted-prime shadows for all events of those small windows and the first 64 sources of each larger window (13,481 post-event comparisons including nonreturns). It also checks the recharge lower bound and three short-gain values, the prefix origin span, and exact repeat decomposition. The larger windows contain all original sources, not a sample, for the tail and prefix statistics; shadow crosschecks are only a subset as described. Values are finite, not proof of asymptotic estimates.

| X | B | max T_2k/T_k growing cutoff | fixed p>7 | p>19 | p>4P_growing |
|---:|---:|---:|---:|---:|---:|
|256|43|.447826|.323944|.144737|0|
|1024|85|.227219|.0962464|.0191388|0|
|4096|170|.336226|.204983|.0908179|0|
|16384|339|.352394|.218107|.094784|0|
|65536|678|.372176|.235322|.106939|0|
|262144|1355|.315821|.246368|.115138|.00266809|
|1048576|2710|.338371|.259695|.130371|.0000567263|
|4194304|5419|.364256|.273517|.140746|.000476635|

Zero denotes no positive doubling ratio (sometimes the band itself is empty). At X=4194304 and growing y=5, T_1=21544762, T_2=6813417, T_4=2481826, T_8=704926, T_16=116583, T_32=5102. Maximum full multiplicity 62. The fixed LOW7 results at the largest X have P=712, Q=2646, a=2, D=11810091, A=3878989, R_1=0, R_>=2=142. At X=262144,1048576,4194304 the large multi-donor counts are 40,5,142. No large one-donor returns in these finite runs with this Q; this observation is not used in the proof. Q>=840 only in the last two windows. At X=4194304 D/(XP/2)=~0.00791. The finite 2P clock prerequisite need not yet hold.

Status: PARTIAL. New mathematical one-donor bound proved on paper; no new Lean compilation; actual MIN aggregate contraction and the remaining asymptotic estimates are open.
