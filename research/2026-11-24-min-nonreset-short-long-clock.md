# Exact short/long clock classification of low-height nonreset events

2026-11-24 JST. Continues 5cd31abf7c35cfdc0125470a23769af6b5f3f238 on the SAME research/min-cycle-forest-2026-11-24 branch. Elementary paper lemmas and exact finite audit; not Lean-checked. No solution of the full first-excursion tail, reset saturation or twin-prime conjecture. No novelty claim about external literature.

## 1. Exact clock formula at low height

Use MIN as in the preceding notes: even horizon C, current time t, nonnegative height h=2t-C, eligible odd primes q<=B dividing C-1 or C+1; r(C) is the least such prime, and the earliest clock is selected, resolving ties by smallest prime. For q>=7 define sigma_q=-1 if q|C-1, +1 if q|C+1 (these are mutually exclusive), b_q=0 on the minus/even-clock side and 6 on the plus/odd-clock side. Write m_q=(C+sigma_q)/q, an odd integer.

Define k_q=0 or1 by the exact parity rules:
    sigma=-1: k_q=0 if m_q=3 mod4, 1 if m_q=1 mod4;
    sigma=+1: k_q=0 if m_q=1 mod4, 1 if m_q=3 mod4.
Put
    n_q=(C+q-1+b_q)/2+k_q q.
Then n_q is the first eligible clock strictly after t whenever q-1>h (and q>=7). Indeed on the minus side its expression is q(m_q+1+2k_q)/2, which is even multiple of q exactly for the stated k_q. On the plus side it is q(m_q+1+2k_q)/2+2, which is congruent to q+2 mod2q exactly for the stated k_q. Both candidate base times are strictly above t because q-1>h. The preceding clock is at n_q-2q, at most (C-q-1+b_q)/2<=C/2<=t since q>=7. This is exact even if the candidate lies beyond the current cutoff (in which case it cannot be selected).

If a selected high p>7 is nonreset (post-height not b_p) and h<r(C)-1, then r>=3. In fact r>=7: if r=3,5 then h<r-1 and the wait bound n-t<=2r gives h'=h+2(n-t)-(p-1)<5r-p, whereas a high nonreset has h'>=2p, impossible for p>r with r=3,5. Hence all eligible q satisfy the short/long formula. In particular the selected p has k_p=1 and its post-height is exactly b_p+2p. If any q<p were eligible, then
    n_q <= (C+3q-1+b_q)/2 <= (C+3p-1+b_p)/2 = n_p,
since p-q>=2 and b_q-b_p<=6. The first inequality can be equality or strict; either way MIN would choose the smaller q, a contradiction. Thus
    h<r(C)-1 AND p>7 nonreset => p=r(C), h'=b_p+2p.
Equivalently, a high nonreset with p!=r must have h>=r-1.

For an unconditional low-height test, if p>2h+20 then p>7. For a nonreset event h'>=b_p+2p gives
    4r >= 2(n-t) >= 3p-1-h.
Here 4r>=2(n-t) is the clock-gap bound. Consequently r>= (3p-1-h)/4 > h+1, by p>2h+20. The preceding theorem applies. Thus
    p>2h+20 AND nonreset => p=r(C), h'=b_p+2p.
No initial-reset or small prefix-length hypothesis is needed. This strengthens the earlier weaker r>=p/8 bound in the low-height regime. It is not a global equality p=r: numerous high-height nonreset selections have p!=r.

## 2. Exact top-half nonreset classification

Use the common cutoff K=floor((7X-1)/4), B=ceil(sqrt(7X)), X dyadic divisible by4, all reset origins as in the preceding note. Consider any executed event with p>=B/2, p>2h+20, and nonreset. For sufficiently large X, C in [2X,2K], C+1<=B^2/2, C-1>B. By section1 p=r. Every composite neighbor has all prime factors >=p (a smaller factor would be eligible), so, since p^3>B^2/2, has exactly two prime factors with multiplicity. Each is <=B since the other is >=B/2. In particular the selected neighbor is C+sigma=p m, with p<=m<=B and both prime, allowing a square.

All eligible q must have k_q=1: if k_q=0 its clock is (C+q-1+b_q)/2 <= (C+B+5)/2 < (C+3p-1+b_p)/2=n_p for B sufficiently large, a contradiction. Apply the exact cofactor parity rule to BOTH prime factors of each composite neighbor (also valid for a square): on the minus side both factors must be 1 mod4; on the plus side both must be 3 mod4. Thus every composite neighbor is 1 mod4. Since the two odd neighbors differ by2, only one can be composite. The other is genuinely prime. Therefore the only possibilities are
    C-1=p m, p=m=1 mod4 (meaning p congruent m congruent1), C+1 prime,
or
    C+1=p m, p=m=3 mod4 (meaning p congruent m congruent3), C-1 prime,
with p<=m<=B and p>=B/2.
Conversely, given either pattern with p the smaller prime, q>=p for every eligible factor and p>2h+20, both eligible clocks are long, so the earliest selects p (if executed by cutoff) and is nonreset. Thus it is an exact classification of this conditional regime, not a claim all top-band nonresets arise this way. In particular p^2<=C+sigma<=B^2/2; no such nonreset can use p>B/sqrt2.

The candidate COUNT of these distinct horizons (ignoring all reachability, height and mass) is O(X/log^3 B): for each p in [B/2,B], m in [p,B] and pm +/- 2 must both be prime. Use the same uniform dimension-two upper-bound sieve on m and pm +/-2 as in the prior notes, with sieve level a small power of B, excluding p and 2; the slopes are invertible and two roots distinct for the other primes. The interval can be embedded in length B, yielding O(B/log^2 B) candidates per p; sum over O(B/log B) primes p, B^2=O(X). This repeats the strength of the first-top arithmetic sieve on a different, explicitly classified physical regime. It is NOT a bound on the original-source multiplicities arriving at these horizons.

## 3. High-height nonreset physical mergers: product divisibility and a source-level deletion

For any nonreset physical post-state (n,C') with two DISTINCT incoming selected primes p,q>=7, both sides have the SAME clock parity and therefore the same b(n)=0 or6. From the exact post-height divisibility,
    pq divides (2n-C'-b(n))/2.
This quotient is a positive integer for nonreset high events. Hence h'=2n-C'>=2pq+b(n). More generally the product of any distinct incoming high labels divides this quotient. This excludes simultaneous distinct large incoming labels at low nonreset heights, without a bound on their predecessor masses. It is not a statement about projected-key contacts occurring at different actual times, and does not constrain reset mergers.

For a source-weighted use, return to the canonical full-window (or restricted common-cutoff) uniform projected high-key stopping process of the earlier first-heavy notes, with T=ceil(B) and LOW7. Its executed prefix cost R_pre=O(X^2/log^3 B)+O_L(X B log log B)=O(X^2/log^3 B) for large B; the second term is absorbed. For every original tag, h<=6+4 R_pre(tag) at any attained physical state, because C never decreases and elapsed<=2R_pre(tag). Let Q=B/log^a B with fixed 0<a<3/2. If a tag attains a nonreset physical state which has two distinct executed incoming high labels >=Q, then its own accumulated cost is >=(2Q^2-6)/4, even if its own last label was smaller. Therefore the number of DISTINCT tags ever attaining any such state is
    O(R_pre/Q^2) = O(X/log^(3-2a) B)=o(X).
The witnessing labels can belong to different tags and need not have large masses; this is an all-depth source deletion at any physical merger with two top witnesses. For the earlier stopped-cohort bounded-degree witness pairs (blocks of size <2T), all pairs with at least one such tag are O(T R_pre/Q^2)=o(XT). This conclusion concerns physical merges, not all first PROJECTED contacts. It does not assume that two tags were in a high projected group of mass T at the same time. It uses the projected cap only to bound cumulative pre-stop costs. Reset states, same-label mergers, smaller labels, and asynchronous projected contacts remain.

## 4. Exact finite diagnostics

Executed saved JavaScript function body:
    node research/min_nonreset_short_long_clock_audit.mjs 256 1024 4096 16384 65536 262144 1048576
The audit covers all hypothetical reset origins under common cutoff and their first excursion (not a projected stopping process). At each selected event checks height, clock and gain bounds. For h<r-1, verifies exact earliest-clock expression for every eligible q>=7 (code checks q>5), even those beyond cutoff; independently checks the low-height nonreset least-factor theorem, and for each p>2h+20 nonreset checks p=r, exact post-height, p^2 bound, and top-half classification including primality by exact SPF and both mod4 conditions. All origins retain their own current states; repeated physical visits by different origins are counted as incidences, not distinct keys. At X256/1024 3213 literal parity-GCD clock/terminal decisions. Full script and JSON exact remote readback at f40ae0fa41d04b5511306c8418a609a65a948d6d. Total r-cost agrees with previous first-excursion audit.

|X|B|low-height large jumps p>2h+20|nonreset among them|top-half large jumps|top-half nonreset among them|
|--:|--:|--:|--:|--:|--:|
|4096|170|319|114|83|7|
|16384|339|1723|642|344|85|
|65536|678|8998|3488|1191|240|
|262144|1355|41452|15951|3967|524|
|1048576|2710|185115|72519|14170|2312|

At X1048576, 786429 reset origins, 4680238 events, 1474259 high events, 1101762 high nonreset incidences. 2043763 exact short/long candidate-clock checks. Among the 2312 top-half large-jump nonresets, 835 are on the minus side and 1477 plus; every one satisfies prime/semiprime classification. There are 4964 top-half high nonreset incidences in all, 2652 outside the large-jump hypothesis (so the theorem does NOT cover them); only 4624 of the full 4964 have a prime neighbor. 298138 high nonreset incidences have p!=r, all with h>=r-1. The maximum height in the preceding audit was 14490>B, so a universal height<=B assumption is false. Example u=1058173, t=1058185, C=2116350, h=20, p=1429, n=1060318, h'=2858, C-1=1429*1481, C+1=2116351 prime. Both factors are1 mod4. Exact integer checks, no asymptotic conclusion from finite proportions.

## 5. Remaining proof obligation and priority

The latest reset route has two independent unresolved steps: the unweighted multiple-high FIRST-excursion moment A(X)=o(XB), and enough original sources escaping reset saturation under the cap B (alternatively the early-sink criterion). The earlier projected-key stopping route already has R_pre=o(X^2) unconditionally; it only requires the bounded-degree stopped-cohort far-first-contact estimate P_w/(NT) < 1/2-epsilon along arbitrarily large X. For T=B the elementary stop inequality P_w >= (T-1-floor(T/2)) S gives the final contradiction, using the exact original-root cutoffs. This is a single sufficient residual problem, NOT already established.

Candidate counts multiplied by full parent masses cost T^2. The unconditional CRT count O(X(log log B)^2) yields O(X T^2(log log B)^2) versus the needed O(XT): a factor T (of order B) beyond logarithms. Additional logarithmic sieve savings alone cannot close that gap. A productive next target is a genuine joint-ancestry/first-physical-merge bound, exploiting the exact no-split physical graph and the nonreset product divisibility above, while separately accounting for reset mergers and projected asynchronous contacts. The new short/long classification makes the entrance to a high-height nonreset excursion explicit; it does not bound subsequent height accumulation or mass. No proof of the remaining estimate is obtained; no new branch, no main changes.
