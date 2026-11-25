# Compressed intermediate words and cheap-successor time CRT

2026-11-26 JST. Continues [0fda077cd533](https://github.com/tara-sooo/A166944-Lean/blob/0fda077cd533a8f0cfddb8104e683e1c1ef549e2/research/2026-11-25-min-unified-rough-pair-isolation.md) and [09559cdebe9d](https://github.com/tara-sooo/A166944-Lean/blob/09559cdebe9d44a0a2b5f6a64299e49eeaa1453a/research/2026-11-25-min-unified-deficit-packing.md). The two current independent branch heads were read: [paired LOW compression, e1ad9e2](https://github.com/tara-sooo/A166944-Lean/blob/e1ad9e2b434c652699e1bc9a0797887631e0ea6d/research/2026-11-25-min-clock-paired-low-entry-canonical.md) and [future high witnesses and lag CRT, fa872d9](https://github.com/tara-sooo/A166944-Lean/blob/fa872d9c5c94d683b41081b886a7e58903c0f4fe/research/2026-11-25-min-prime-root-lag-witness-crt.md). Use actual LOW compression and a new within-path, rather than pair-lag, CRT. Two unconditional linear masks: one forces either a diverging intermediate event count or a large radical of intermediate labels; the other forbids an extremely cheap large first nonLOW successor. These narrow the moderate-mass stable high residue. No general bound of that residue or twin-prime proof.

## 1. Original parameters and LOW compression

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^(1/4)), H=T+B, Q=ceil(B/u). Natural HIGH means selected p>=Q and least factor r(C)>p/sqrt(log p). All original prime-root gain-stopped completed paths are unchanged. At each actual occupied tick (j,C), b(C,j) is the original tag mass of completed waits, excluding terminal snapshots; all share a deterministic selected p and exit tick v. The deficit d=2j-C is between 0 and 6+5H; possible clock ticks at a fixed C therefore number O(H). The support of natural HIGH horizons is O(X ell/u^3) by the least-factor quotient sieve. Every actual event has positive wait w<=2r<=3(p-1).

As in the paired LOW compression note, choose P0 the largest even primorial <=ell, for sufficiently large X. Define LOW as selection of an odd prime dividing P0. The maximum gain of any contiguous LOW chain is <P0: it cannot strictly cross a multiple of P0, nor start a LOW jump from a multiple of P0. Thus its actual elapsed time is <3P0. This applies to partial chains and to chains ending at actual terminal snapshots. Here P0 grows slowly, with largest prime factor Y=Theta(log ell); it is distinct from the wide stable-strand primorial P.

Take a natural HIGH event at even C, label p, immediate posthorizon J=C+p-1. Consider any subsequent original rough recorded horizon A, including a terminal snapshot, with roughness meaning no odd factor <R=B^(1/8) in A±1. All natural HIGH prehorizons are rough for large X. Compress the intervening actual completed edges from J to A into the successive nonLOW labels q_1,...,q_h, and the h+1 LOW-chain gains e_0,...,e_h, each an even integer 0<=e_i<P0. Then
    A=C+p-1+sum_(i=1)^h(q_i-1)+sum_(i=0)^h e_i.
The horizon just before q_i is C+a_i, where a_i is explicitly determined by p and the preceding word, and
    q_i | C+a_i+sigma_i, sigma_i in {-1,+1}.
Let D=rad(q_1...q_h) be the product of DISTINCT nonLOW primes, with D=1 for h=0. Repeated q conditions need not be independent: they either agree or make the word impossible.

## 2. Four-form sieve with a growing intermediate word

Define
    k=floor(log u/[8 log(2 ell)]),  D_max=B^(1/2).
For the new relaxed support consider every word with h<=k and D<=D_max, every LOW gain e_i as above and every side sigma_i. The words need not be realizable by MIN. Require the initial p to divide C+sigma, high least-factor condition at C, all q_i congruences, and roughness at the final A in the original O(X) horizon domain. The latter conditions include the actual compressed words just described. Since D<=B^(1/2)<Q eventually, p is distinct from every q_i.

Write C=p(2n+1)-sigma. The congruences on C for each distinct q restrict n to a unique residue mod q; repeated constraints are checked for consistency. Thus either no candidates or one progression n=n0+D t, equivalently C in one residue class mod 2pD. There are O(X/(pD)+1) consecutive t values to sieve. With G=A-C, the four forms on a=2n+1 are
    a, p a-2 sigma, p a+G-sigma-1, p a+G-sigma+1.
All must avoid odd prime factors <R. The initial quotient is rough since p itself exceeds R. The four form offsets are distinct eventually because G>=p-1 and p grows; all differences are O(k B+(k+1)P0+B), with logarithm O(u). In the variable t the coefficients include D. Outside primes dividing pD and the product of the nonzero offset differences, and 2,3,5, exactly four residue classes are forbidden. The logarithm of this nonzero excluded product is O(u) uniformly even for h<=k, since log D<=u/2. This is the same dimension-four sieve as in the previous note, on a progression of smaller length. Its exceptional-prime product loss is O(ell^4), uniformly.

Use the self-contained Selberg upper bound of 0fda077 with z=floor(B^(1/40)); its error O(z^8)=O(B^.2) is absorbed because X/(pD)>>B^.5 and the logarithmic factor is harmless. Hence for each fixed word, signs, LOW offsets, p, sigma the count of C is
    O(X ell^4/(p D u^4)).                                      (1)
The constants are uniform in word length h<=k. No extra sieve dimension is claimed from the individual q congruences; they give the divisor D in the denominator of the progression length.

For every h, sum 1/D over all ordered h-tuples of odd primes <=B, ignoring the radical bound to upper bound this sum. Appending a label already in the word gives at most h choices at no new denominator cost; appending a new label has total reciprocal-prime weight O(ell). Starting with the empty word gives
    sum_words 1/rad(q_1...q_h) <= (C ell+h)^h
for an absolute C. This handles repeats without using the invalid denominator product q_1...q_h with multiplicity. The side choices cost at most 2^h and LOW offsets at most (P0+1)^(h+1). For all h<=k their total weighted count is at most
    (k+1)(P0+1)[2(P0+1)(C ell+k)]^k
      <= u^(1/4+o(1)) <= u^(1/3).
Indeed P0<=ell, k<=log u/(8 log(2ell)), and the logarithm of the bracket is 2 log ell+O(1). Summing (1) over p>=Q (reciprocal sum O(ell/u)) and the two initial sides shows that the number of relaxed arithmetic candidates, counted with their words, is
    O(X u^(1/3) ell^5/u^5).                                    (2)
In particular both the support of initial C and the support of final rough A are bounded by (2). These bounds count horizons, not tags or actual clock phases.

## 3. Linear word mask and a forced future rough witness

Use Mstar=2u^(7/3)/ell^2, as in the previous moderate-strand note. Pay all natural HIGH actual clock at an initial horizon in (2) with b(C,j)<=Mstar. Optionally also pay all completed clock (any selected label) on the final rough support of (2) with that same mass cap, by priority. Since there are O(H) ticks per horizon, the union of both masks costs
    O(Mstar H X u^(1/3) ell^5/u^5)
       = O(NT ell^3/u^(4/3))=o(NT).                            (3)
No pair weight or separate asynchronous estimate. An actual retained high tick of a stable strand g with n_g<=u^(7/3)/ell^2 has b<=Mstar by the original entropy property. For every subsequent original rough recorded horizon in its own prefix, its compressed intervening word must therefore satisfy
    h>k OR D>B^(1/2).                                          (4)
This is an actual chronology statement, not just an assertion about possible arithmetic labels.

In the second case with h<=k and h>0, at least one intermediate selected prime exceeds B^(1/(2h))>=B^(1/(2k)). This grows faster than every fixed power of u. More generally if h=1 the sole nonLOW intermediary must exceed sqrt(B). In the first case the number of nonLOW events tends to infinity (k=Theta(log u/log log u)); their gain is at least (k+1)(Y-1), but is not necessarily comparable to B. These alternatives do NOT imply that all inter-high gain exceeds a fixed power of B.

To remove the vacuous case of no later high, apply a fixed additional endpoint trim within each original central superblock: pay high events whose own block final actual posthorizon is <C+s0, s0=ceil(B^1.5). At most O(s0+B) gain per source block is affected, hence actual clock cost O(N(H/S+2)(s0+B))=o(NT) for S~H/(4u ell^2). Use the previous sparse witness property (or re-freeze the measure after (3) and the next mask, reapply sparse deletion at one additional O(NT/u^.25) cost). The interval from C to the first actual recorded endpoint >=C+s0 in that block contains the current event and has length in [s0,s0+B]. It contains Omega(u^(7/4)) distinct contributing high labels, hence a later natural HIGH event for large X. Thus every surviving moderate high incidence after this endpoint trim has an actual later rough high prehorizon within s0+B, and (4) applies to the FIRST such natural high successor. The witnesses are in the specified frozen measure, not necessarily retained after all deletions. The endpoint trim and repeated sparse cover are paper deductions, not tested by the new standalone audit.

## 4. A second CRT: eliminate cheap large first nonLOW successors

This new constraint uses departure ticks, not the spatial support (2). At an actual high jump (C,p,v), suppose its first subsequent nonLOW event has selected q>=B^(1/8), preceded only by LOW chain of gain e<P0. Its prehorizon is A=C+p-1+e, and the label q divides A+tau for a unique tau in {-1,+1}. Let theta=u^(-3/4). If this event has actual wait w_q<=theta q, its departure tick v' satisfies
    1<=h=v'-v<=3(P0-1)+theta q.
The departure residue for a label a dividing horizon+sign is 0 mod 2a for sign -1 and a+2 mod 2a for sign +1. Thus
    v=phase(p,sigma) mod 2p,
    v=phase(q,tau)-h mod 2q.                                 (5)
Here p!=q: if equal, p divides A+tau-C-sigma=p-1+e+tau-sigma, which is p plus a nonzero odd integer of magnitude <=P0+3<p (e even). The conclusion holds even when the sign changes. For each positive h allowed above, (5) either has no solution (parity mismatch) or fixes v modulo 2pq. As v lies in an interval of length O(H) at a given C, the number of possible v is O(H/(pq)+1) per h. The h range has O(theta q) integers uniformly because q>=B^(1/8)>>P0/theta. All occupied tick states of the high waiting slot with this v lie in [v-2p,v). Consequently for a fixed C,p,e,q the total number of candidate high tick states is at most
    O(p theta q (H/(pq)+1))=O(theta(H+pq))
       =O(theta H(1+u^.25)).                                 (6)
The last inequality uses pq<=B² and H=Theta(B²/u^.25). This count includes all possible actual arrivals into the slot, with no multiplier for their number. It is independent of the arithmetic four-form support.

At a high horizon there are at most four possible high p (each C±1 has at most two primes >=Q). For each of the O(P0) possible e, the two integers A±1=O(X) have only O(1) prime divisors >=B^(1/8), by their size. The number of high horizons is O(X ell/u³). Pay every candidate high tick in the union of (5), with original mass b<=Mstar. This is an overcover defined by original C,p,v and possible q,e,h, whether the future event actually occurs or not. The total cost satisfies
    W_time << Mstar (X ell/u³) P0 theta H (1+u^.25)
           = O(NT u^(-1/6))=o(NT),                           (7)
since P0<=ell. In particular, on any surviving moderate high incidence with first nonLOW successor selected q>=B^(1/8), its actual wait must be >q/u^.75. The result is not a relative-expensive predicate on least factor r alone, but a lower bound on actual elapsed wait, using the two-label phase lattice and LOW elapsed time.

Combining (4) and (7), if there is exactly ONE nonLOW event between a surviving moderate high hit and its next natural high event, then that intermediate q>sqrt(B) and its actual wait is >sqrt(B)/u^.75. The case h=0 is excluded entirely. The single-intermediary conclusion substantially exceeds the former polylogarithmic gain bound, but for multiple intermediaries the first large label need not be the first nonLOW event, and for many nonLOW events only the count alternative is proved. Even sqrt(B)/u^.75 is o(B), so this does not supply a constant proportional charge against an arbitrary high wait. All these are masks on original paths, not modified dynamics.

## 5. Sufficient target and unresolved sector

Apply the new masks (3), (7) and the optional fixed extra sparse and endpoint trims by priority to the previous actual clock ledger. The previous sufficient condition remains
    liminf_(dyadic X -> infinity) (A_rem+L_rem)/(NT)<1/2,
where A_rem is exact remaining non-HIGH clock and L_rem the exact remaining high clock. The new residuals are subsets of the previous ones. In particular the new arithmetic exclusions do not add an async energy assumption. For moderate high strands combine long nonRESET span, local many-label and nonzero-phase witnesses, the prior short rough-landing isolation, and (4),(7). Large-mass stable strands still need a separate bound, as does the non-HIGH residual. The growing-word sieve is an unconditional extension of the preceding fixed-offset approach, but not a proof of full contraction. No external novelty claim or Lean kernel check.

## 6. Reproducible finite audit

Source [min_unified_intermediate_word_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/56f3703bcef79c174fc84b3a872fa12126e33670/research/min_unified_intermediate_word_audit.mjs), exact remote readback verified, commit 56f3703bcef79c174fc84b3a872fa12126e33670. Executed its audit function in the available ECMAScript runtime, not a separate Node process. Reproduce:
    node research/min_unified_intermediate_word_audit.mjs 256 1024 4096 16384 65536

Five passing standalone diagnostic runs: P0=6 (LOW label3), k=2, D_max=floor(sqrt B), large q>=ceil(sqrt B), theta=.2, Mstar=8, T=min(8B,floor(X/2)), Q=max(5,ceil(B/10)), HIGH r>p/2, R=max(3,min(ceil(sqrt B),ceil(Q/2))). The finite large threshold and all other diagnostic parameters differ from analytic scaling. For small X, where p<=D_max or p<=P0+2 may occur, the corresponding mask is restricted to p>D_max or p>P0+2 respectively. No analytic estimate of support constants from these runs.

Enumerates relaxed words by actual spatial divisors at each offset, checks exact congruences for every word reaching roughness, and checks actual original first rough witnesses within the word bound. For time support, lists every candidate q and offset and tests whether its first possible residue after v lies within 3(P0-1)+theta q. That existence test is equivalent to existence of a positive h in (5); it can overcover an actual later q exit. Independently checks actual first nonLOW large and cheap successors. Counts exact original tick mass and priority clock partition for initial word and time masks. The final rough-support deletion, stable-strand reconstruction, extra endpoint/sparse masks, asymptotic counting estimate and independent literal gcd oracle are not audited in this new script.

| X | raw HIGH | word paid | time paid (disjoint) | remaining HIGH | actual nonempty word witnesses | actual cheap successor witnesses |
|---:|---:|---:|---:|---:|---:|---:|
|256|1765|1303|0|462|0|14|
|1024|3908|3564|0|344|2|19|
|4096|37458|33277|721|3460|332|67|
|16384|195474|103402|12653|79419|624|214|
|65536|1380549|531796|59761|788992|1578|335|

At X65536: 5709 prime roots, 140255 completed events, 578522 occupied tick states; original clock2395330. Relaxed initial support3581, 8732 rough-reaching words including7284 nonempty words, 8351 nonLOW congruence checks, 26163 enumeration steps, 23205 time candidates, 3965 actual short word witnesses of which1578 nonempty, 335 actual cheap first large nonLOW witnesses and1459 expensive. 185572 distinct high tick states paid by word mask, 21122 further by time mask, remaining high clock788992 including71727 at original mass<=8. The reductions are from the original diagnostic ledger only; no cumulative comparison or asymptotic inference. Main and independent branches unchanged.
