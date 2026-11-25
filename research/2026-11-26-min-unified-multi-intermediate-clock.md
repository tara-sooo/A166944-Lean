# Near-linear intermediate radical and cumulative clock CRT through the first large intermediary

2026-11-26 JST. Continues [d0cdbdadf663](https://github.com/tara-sooo/A166944-Lean/blob/d0cdbdadf6634e25fa9329d01ece2a68f9a877bc/research/2026-11-25-min-unified-intermediate-word-crt.md), with [the four-form sieve](https://github.com/tara-sooo/A166944-Lean/blob/0fda077cd533a8f0cfddb8104e683e1c1ef549e2/research/2026-11-25-min-unified-rough-pair-isolation.md), and [the deficit-adaptive stable-strand masks](https://github.com/tara-sooo/A166944-Lean/blob/09559cdebe9d44a0a2b5f6a64299e49eeaa1453a/research/2026-11-25-min-unified-deficit-packing.md). Current independent heads read: prime-root [e1caa3e36489](https://github.com/tara-sooo/A166944-Lean/blob/e1caa3e36489ec286b41e9e4ffbb17519d6cca8b/research/2026-11-26-min-prime-root-projected-diamond-halos.md), stable-heavy e1ad9e2b434c (paired LOW compression, read in the parent turn, unchanged). The prime-root diamond lemma uses two paths, whereas this note concerns consecutive HIGH events on one original path. New unconditional linear removals on the same moderate-mass original stable strands. No new pair energy premise. No Lean compilation, no twin-prime proof.

## 1. Parameters

As before, dyadic X, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u), HIGH means selected p>=Q and least eligible r(C)>p/sqrt(log p). Original actual completed paths and cutoff are unchanged. At each occupied completed tick (j,C), b(C,j) is its original tag mass, excluding terminal snapshots. The deficit bounds 0<=2j-C<=6+5H give O(H) possible ticks per horizon. Every original selected gain is p-1, wait w<=2r<=3(p-1). The original high-horizon support is O(X ell/u^3).

Use the same small even primorial P0<=ell (largest such), LOW labels dividing P0, and
    k=floor(log u/[8 log(2 ell)]),     Mstar=2u^(7/3)/ell^2.
For large X, k>=1 and a LOW chain has gain <P0 and actual clock <3P0. The original stable through-cohort g with n_g<=u^(7/3)/ell^2, after the entropy trim, has b(C,j)<=Mstar at every retained focal tick. All new masks use this original mass, not the mass after other masks.

A word between a HIGH jump and a subsequent R-rough recorded horizon, R=B^(1/8), consists of h nonLOW labels q_i separated by h+1 LOW gain offsets 0<=e_i<P0, even. Its radical D is the product of DISTINCT q_i, with empty radical 1. The parent proved the uniform weighted combinatorial bound
    sum_(h<=k, words and side choices and LOW offsets) 1/D <= u^(1/3)       (1)
for sufficiently large X, even when the radical restriction is omitted. The stronger estimate u^(1/4+o(1)) also holds. Repeated labels are counted by their radical, not multiplicity. The initial selected p and its side are not counted in (1).

## 2. New radical cutoff B exp(-u^.75)

Replace the old radical cutoff sqrt(B) by
    Dstar=B exp(-u^(3/4)).
For large X, Dstar<Q, so p is distinct from every q_i in a word of radical <=Dstar. For fixed p, sign sigma, intermediate word and offsets, all nonLOW congruences either conflict or restrict C=p(2n+1)-sigma to one progression in n of modulus D. The actual horizon distance G from C to the final rough horizon is fixed by the word. On that progression the four forms
    a=2n+1,  p a-2 sigma,  p a+G-sigma-1,  p a+G-sigma+1
must all avoid odd prime divisors <R. Their offsets are distinct, since G>=p-1 and p grows. Drop primes 2,3,5 and divisors of pD and the product of the nonzero offset differences, whose logarithm is O(u). Exactly four distinct forbidden residue classes remain per good prime.

The progression has length O(X/(pD)+1); X/(pD)>>exp(u^.75). Apply the previous explicit dimension-four Selberg bound at z=floor(exp(u^.75/40)). Its error O(z^8) is absorbed uniformly into X ell^4/(pD u^3). The product lower bound in that proof is now >> (log z)^4/ell^4 >> u^3/ell^4: its excluded-prime loss is still O(ell^4), since the product of bad primes has logarithm O(u). Thus for each word and p, sigma
    # C << X ell^4/(pD u^3).                                  (2)
This does not use a four-dimensional asymptotic for prime tuples. Summing (2) with (1) and sum_(p>=Q)1/p=O(ell/u) yields total support of initial horizons, and also of final rough horizons, at most
    O(X u^(1/3) ell^5/u^4).                                   (3)
A fixed initial p,C can have many words; counting all words only enlarges this support.

Remove all actual HIGH ticks on the initial support with b<=Mstar. Optionally also remove all completed ticks on the final support with b<=Mstar, by disjoint priority. The cost is
    W_rad << Mstar H X u^(1/3) ell^5/u^4
           = O(NT ell^3/u^(1/3))=o(NT).                       (4)
Indeed 7/3+1/3-4+1=-1/3. This is an unconditional extension of the former sqrt(B) mask: its support contains the old one, with the same mass cap and word lengths. The former smaller cutoff had a better rate for its cost but leaves a larger residual. The exponent 3/4 is a convenient choice: using exp(-u^a) with any fixed 2/3<a<1 gives the same argument with ratio O(ell^3 u^(8/3-4a)). No claim of optimality.

Hence for each surviving moderate-mass HIGH focal incidence and every later original R-rough recorded horizon in its prefix, either h>k or D>Dstar. In particular if the next actual natural HIGH event exists and has exactly 1<=h<=k intermediate nonLOW labels, at least one label exceeds
    R_h = Dstar^(1/h)=B^(1/h) exp(-u^.75/h).                    (5)
The case h=0 is completely paid. With a single nonLOW intermediate, q>Dstar=B^(1-o(1)), a much stronger lower bound than sqrt(B). This concerns the actual selected label, not necessarily the least eligible factor or actual wait.

## 3. Spatial support for a short prefix before the first label above R_h

The parent time CRT only handled a first nonLOW event (possibly preceded by LOW). To handle arbitrary position, fix h in [1,k], and consider a prefix of at most h-1 nonLOW labels, each <=R_h, with their sides and LOW offsets. At its end there is a possible label q>R_h. Only this FIRST large-label position matters. The prefix radical D0 satisfies
    D0 <= R_h^(h-1) <= B^(1-1/h).
For h=1 the prefix is empty and D0=1. All prefix labels are <Q for large X, including the empty h=1 case. Given p,C and this prefix word, the horizon A before q is fixed. Let E=A-(C+p-1); for h>=2,
    0<=E<= (h-1)R_h+hP0 <= k sqrt(B)+kP0=o(Q);
for h=1 E<P0. It is even. The candidate q cannot equal p, since then p divides
    A+tau-(C+sigma)=p-1+E+tau-sigma,
which is p plus a nonzero odd integer of magnitude <p, for large X. It also cannot equal any prefix label, by the threshold choice. Thus a genuine two-prime time CRT will always apply. This is independent of the actual elapsed time of the prefix.

For fixed p, sigma, and prefix word the spatial congruences restrict C to one residue class mod 2pD0 or are inconsistent. Retain only initial high roughness of a=(C+sigma)/p and C-sigma, a two-form upper-bound sieve on that progression. Its quotient length satisfies X/(pD0)>>B^(1/h)>=B^(1/k). Use z=floor(exp(u/(40k))). The explicit Selberg construction in the four-form note works with 2 forbidden residues instead of 4; replace omega(d)=4^omega_number(d) by 2^omega_number(d), G lower bound by (log z)^2/ell², and keep the error O(z^8). The excluded product (pD0 times the nonzero offset difference) has log O(u), so the bad-prime loss is O(ell²) by the same Mertens argument. The error is absorbed uniformly, since z^8<=B^(1/(5k)). Therefore
    # C << X k² ell²/(pD0 u²).                                 (6)
There is no roughness assumption on A, nor a sieve applied to an arbitrary unknown trajectory. The only counted objects are relaxed prefix words and the initial high horizon.

For a fixed h, summing (6) over all prefix words (including every final LOW offset) with (1) and over the initial p, sigma gives
    # (C,p,prefix) << X k² ell³ u^(1/3)/u³.                     (7)
The actual future q must divide A-1 or A+1. Since q>R_h and log R_h=(u-u^.75)/h >=u/(2k) eventually, and A is in the O(X) original horizon domain, the number of possible DISTINCT such labels is O(k) per key (use the product of distinct prime divisors of the two integers). This is a deterministic arithmetic count, not an assumption about their density. Include every such q and its unique side tau. Summing over all h<=k costs one further factor k. Counting duplicate keys only increases the upper bound.

## 4. Cumulative clock CRT, not a per-event clock assumption

Put theta=u^(-5/4). At an original actual HIGH jump with exit tick v, let v' be the exit of the first nonLOW label q>R_h in a prefix of at most h-1 smaller nonLOW labels. Its total elapsed time after the initial high exit is t=v'-v, including ALL intervening LOW and nonLOW waits through the selected q. If t<=theta q, the exact parity departure residues imply
    v = alpha(p,sigma) mod 2p,
    v = alpha(q,tau)-t mod 2q,
where alpha(a,-1)=0 and alpha(a,+1)=a+2. Since p!=q, for each positive integer t<=theta q the conditions are inconsistent or fix v mod 2pq. The possible initial exit times lie in an interval of length O(H) at fixed C, using the deficit bound. There are at most O(H/(pq)+1) such v per t. Every occupied tick of the initial high waiting slot lies in [v-2p,v). Thus the total possible initial occupied tick states per candidate key is at most
    O(p theta q (H/(pq)+1))=O(theta (H+pq))
                           =O(theta H (1+u^.25)).              (8)
This is an upper bound even if many earlier recorded arrivals into that same slot occur. It counts actual-clock states, not ancestor labels or pairs. Crucially there is NO assumption that the individual preceding waits are short relative to their selected primes. The hypothesis to be excluded is the total elapsed time through q.

For each candidate key counted in (7) and for all possible q and h, pay all initial HIGH ticks allowed by these residue conditions with original b<=Mstar. This relaxed mask is computable from original C,p,v and possible prefix words, without knowing the later actual trajectory. Its union with (4) is paid by priority. By (7)-(8),
    W_cum << Mstar X k^4 ell³ u^(1/3)/u³
                   * theta H (1+u^.25)
           = O(NT k^4 ell/u^(1/3))=o(NT).                      (9)
The normalized exponent is 7/3+1/3-3+1+.25-1.25=-1/3, with ell³/ell²=ell. k grows only logarithmically in u, so the stated ratio tends to zero. This counts every position of the first large label up to h and every h<=k simultaneously; there is no repeated budget per actual gap.

Consequently if a moderate HIGH focal tick survives both masks and has a next natural HIGH event with 1<=h<=k intermediate nonLOW labels, define q to be the FIRST such label exceeding R_h (5), which must exist by the radical exclusion. Write W_gap for the actual total waits of ALL completed intermediate events between the two HIGH jumps, excluding both HIGH waits themselves. Then
    W_gap >= v'-v > theta q > theta R_h
          = B^(1/h) exp(-u^.75/h)/u^(5/4).                    (10)
The first inequality holds because the chosen q is an actual intermediate event. The argument works even if this first large label is preceded by several small nonLOW labels with substantial elapsed time; that time is part of W_gap. It does not prove a lower bound on w_q alone in that situation.

For h=1 the previous first-nonLOW time mask is stronger (theta_old=u^(-3/4), q>=B^(1/8) eventually). Retain that old mask, giving
    h=1: q > B exp(-u^.75),   W_gap >= w_q > B exp(-u^.75)/u^.75.    (11)
For any fixed h>=2, (10) is B^(1/h-o(1)); for h<=k even its smallest guaranteed lower bound grows faster than every fixed power of u. This generalizes the previous single-intermediary result to a growing number of intermediaries. It is not a claim of an Omega(B) clock lower bound.

## 5. Disjoint transfer to actual non-HIGH gaps, and what is still needed

The earlier fixed future-room trim and sparse-interval witness condition guarantee a next actual natural HIGH event on each remaining moderate strand, by paying o(NT) actual clock (see d0cdbdad section 3). If desired re-freeze the natural high measure after the new masks and repeat the sparse deletion ONCE, also at absolute o(NT) cost. This preserves local diversity and the existence of future witnesses. The prior entropy, deficit and other masks continue to apply; never add a pair energy payment to this linear ledger.

For an original tag, the completed gaps between CONSECUTIVE natural HIGH events are disjoint. Even if a later high event is already marked by another mask, define the gap using the original list. The actual retained clock of the preceding high event is <=2p. Let L_short be the retained moderate high clock with 1<=h<=k. For its own gap let q be the first label above R_h. From (10),
    L_short <= sum_(associated original gaps) (2p/(theta q)) W_gap.    (12)
Each gap is used at most once on its own original tag. For h=1 use theta_old in (12). In particular for any fixed lambda>0, the sector where q>=lambda p has
    L_short,comparable <= (2/(lambda theta)) W_gap,comparable.
The right side includes actual original non-HIGH waits, even if they were already paid by earlier masks. If a bound is only on the remaining non-HIGH ledger, the paid portions must be restored at the relevant weighted rate; an unweighted o(NT) removal is not sufficient to multiply by a diverging factor. This disjoint transfer is a precise conditional estimate, not an unconditional small-o estimate of L_short. It gives a concrete joint HIGH/non-HIGH target for the comparable-label sector, rather than separate pair moments.

The former sufficient condition
    liminf_(dyadic X -> infinity) (A_rem+L_rem)/(NT)<1/2
is unchanged on the smaller exact residual after (4),(9). The new moderate HIGH residual is divided into h>k gaps, and h<=k gaps with (5),(10), with h=1 satisfying (11). For all h<=k the gap waiting time lower bound can be much smaller than p (especially h>1). The factor in (12) can diverge faster than any fixed power of u. Therefore this does not by itself turn a non-HIGH o(NT) estimate into a HIGH o(NT) estimate, nor prove the required strict threshold. Very thick stable cohorts beyond Mstar and the full remaining non-HIGH clock remain open. No proof of twins or external novelty claim. Main and independent branches are unchanged.

## 6. Reproducible diagnostic audit

Source [min_unified_multi_intermediate_clock_audit.mjs](https://github.com/tara-sooo/A166944-Lean/blob/16f0b88c8b4e304e1b5b5d704e253ad0312fe983/research/min_unified_multi_intermediate_clock_audit.mjs) at 16f0b88c8b4e304e1b5b5d704e253ad0312fe983, exact remote readback verified. Executed the audit function in the available ECMAScript runtime, not a separate Node process:
    node research/min_unified_multi_intermediate_clock_audit.mjs 256 1024 4096 16384 65536

Five successful isolated finite diagnostics. Parameters T=min(8B,floor(X/2)), P0=6, k=2, Dmax=floor(B^.8), theta=.4, mass cap8, Q=max(5,ceil(B/10)), HIGH r>p/2, R=max(3,min(ceil(sqrt(B)),ceil(Q/2))). Dmax and theta are diagnostic substitutes, not the analytic values. To preserve the large-X geometric conditions in small tests, restrict both masks to p>Dmax and p>k(P0+sqrt(Dmax))+3. The restriction matters for interpreting small-X results. Compare the extended support to the sqrt(B) support under EXACTLY this same p restriction, not the earlier standalone audit.

Enumerate all relaxed spatial words by divisor lists, verify their individual spatial congruences and radical, enumerate possible q>R_h following every prefix of length <=h-1 with all labels <=R_h, verify p!=q and actual prefix congruences. Compare the time predicate with explicit positive integer t search on up to 5000 occupied states per run. On original paths check actual consecutive natural HIGH gaps, exact gain and total elapsed wait, spatial support for every eligible short word, first label above threshold when radical exceeds Dmax, actual departure phase CRT, cheap cumulative-clock support, and the lower bound (10) on any surviving low-mass focal incidence in this sector. The latter check is positive only once in the largest diagnostic; many actual short gaps are covered by the relaxed spatial/time masks. No full stable-cohort reconstruction, entropy mask, future-room/sparse cover, backward support deletion, literal gcd oracle or asymptotic sieve-constant audit in this script.

| X | raw HIGH | sqrt(B) word paid (same p restriction) | extended word paid | additional cumulative time paid | remaining HIGH |
|---:|---:|---:|---:|---:|---:|
|256|1765|31|31|0|1734|
|1024|3908|886|886|0|3022|
|4096|37458|14949|15448|114|21896|
|16384|195474|52743|65063|922|129489|
|65536|1380549|315787|377458|10854|992237|

At X65536: 5709 prime roots, 140255 completed events, 578522 occupied true ticks, original clock2395330. The extended word support has2544 (C,p) keys, old restricted support1981; 14510 words including10192 above sqrt(B), 22927 spatial congruence checks. Time support2828 (C,p) keys,56562 candidate occurrences,39425 prefix congruence checks,5000 literal time checks. Actual short word witnesses743, including130 above sqrt(B). Actual larger-radical gaps64, all with two nonLOW events, of which35 have the first large label NOT first in the nonLOW list;9 cumulative-cheap witnesses and64 exact actual time-phase checks. One surviving low-mass actual gap checked (10), ratio W_gap/q=.842105>theta=.4. Extended word mask pays61671 more actual high clocks than the restricted old cutoff; further time mask pays10854. All masks counted with priority. This demonstrates genuine multi-intermediary geometry at finite scales; it is not an asymptotic estimate, and does not establish the full sufficient condition.
