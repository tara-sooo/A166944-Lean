# Narrow-band support and the mixed-gain resource bound

2026-11-25 JST. Continues af03d824ea5e89df8ae2b0ee0829a9edcbd379d9 on the SAME research/min-cycle-forest-2026-11-24 branch. New deterministic bounded-support theorem with arbitrary interspersed labels controlled only by their TOTAL gain, plus an unconditional first-selection cluster estimate. Exact finite structural audits. No external search or Lean compilation. This is local gain-resource control, not a bound on the whole signed repeat bank or physical far-coalescence.

## 1. Mixed-gain word, with no LOW cutoff required

Use the common CRT ghost from the prior notes, or simply a relaxed word of executed labels. Each odd prime p has a fixed initial horizon coordinate c_p mod p. At a pre-gain g it can execute only if c_p+g == +/-1 mod p, and then adds p-1. Gain is an even nonnegative increasing integer. No clock priority or time bound is needed in the deterministic argument.

Fix P>=16, a width Delta>=0, and an interval I=[P,P+Delta]. Consider the subsequence of events in I in any contiguous part of a path, and allow all other events between them. Let D be their total off-band gain between the first band event and the last band event, excluding the band jumps themselves. It is the sum of p-1 over off-band events, hence even and nonnegative. We do not require these events to be LOW-only, to lie below a fixed primorial cutoff, to have short waits, or to have bounded number. In the relaxed version, simply insert arbitrary nonnegative even increments between successive band events. Count only the band events as the word length. For at most k distinct band labels, put
    C_1=1, C_k=4+5 C_(k-1)=2*5^(k-1)-1 for k>=2.
The following theorem holds:
    if D<=floor(P/4),
       Delta<=P/[4(C_(k-1)+1)] (for k>=2),
       and at most k distinct band labels occur,
    then the band word length is at most C_k.
For k=1 no width restriction is needed. The theorem is deliberately conservative; it does not claim C_k is optimal. For k=2 the bound is 9; the previous seven-event theorem remains sharper under its original hypotheses.

## 2. Proof by induction on the support size

For k=1, any two consecutive occurrences of the one label p>=P have pre-gain difference p-1+d with 0<=d<=P/4 even. The difference is even. Its residue modulo p is represented by d-1, an odd integer in [-1,P/4-1]. It cannot be congruent to 0 or +/-2 mod p, since its absolute value is <p-2 and it is odd. Thus there is at most one event.

For k>=2, suppose the theorem holds at k-1. If the support is smaller than k, apply the preceding result (the width restriction here is stronger). Otherwise let p be the smallest band label actually appearing. Before its first appearance, after its last appearance, and between consecutive p appearances, the band subword uses at most k-1 other labels. The same width condition is sufficient for the preceding theorem, and the off-band gain of each such subword is <=D. Hence each of those subwords has length at most C_(k-1).

Between two consecutive p occurrences write q_1,...,q_j for the band labels strictly between them, all >p. Let d be the intervening off-band gain. The pre-gain difference is
    (j+1)p + E,
    E=sum_(i=1..j)(q_i-p) - (j+1) + d.
It must be congruent to the difference a of the two actual p eligibility signs, so a in {-2,0,2}. We have j<=C_(k-1), E>=-1, and E<=j Delta +D <=P/2. Because p>=P>=16, |E|<p-2, and hence E=a exactly. Since q_i-p and d are even, E has parity j+1. Thus j is odd and in particular j>=1. Now q_i-p>=2 implies
    E>=j-1+d>=0.
All successive p eligibility signs are therefore nondecreasing. The sum of E over consecutive p returns telescopes to at most 2; in particular there is at most one strictly positive E (necessarily 2), and the total off-band gain between first and last p is at most 2. This is a stronger internal restriction than the external D<=P/4 hypothesis.

If E=0, the inequalities force j=1, q_1=p+2, d=0. Two adjacent zero returns would contain the band pattern p,p+2,p,p+2,p with ZERO off-band gain throughout. The two occurrences of q=p+2 would have pre-gain difference (q-1)+(p-1)=2q-4, whose residue -4 mod q is not 0 or +/-2 for q>=P>=16. Thus adjacent zero returns are impossible. With at most one positive return, there can be at most two zero returns, hence at most three returns in total. There are at most four p occurrences. Combining these with the at most five subwords of at most C_(k-1) other labels gives
    length <=4+5 C_(k-1)=C_k.
This completes the induction. The proof is uniform in the number, size and elapsed time of the off-band events, and does not involve the first selection time of any label.

## 3. Charge long band words to actual mixed-scale gain

Drop the restriction D<=floor(P/4), keep the width and support restrictions. Group the band word consecutively into disjoint complete chunks of C_k+1 band events, plus a final incomplete chunk. By section1, each complete chunk must contain at least floor(P/4)+1 off-band gain strictly between its first and last event. These interior off-band portions are disjoint, so if M is the total band event count,
    M <= C_k+(C_k+1) floor(D/(floor(P/4)+1)).
Consequently
    sum_(band events) p <= (P+Delta) [C_k+(C_k+1) D/(floor(P/4)+1)]
                         <= O(C_k (P+D))
when Delta<=P (including the single-label case with this added harmless width bound).
Every band wait is <=2p in the actual clock process, so the total band completed wait has the same bound up to a factor two. In particular, for fixed k, once the band contains many more than C_k events, its off-band gain must be a positive constant times the total band gain (constant depends on k). This estimates the required resource without counting every event between two returns. It is valid for ALL band events, not only those with a positive signed increment or those already known.

It does NOT imply an o(U) bound on the total repeated waits across many bands: the same off-band gain can be charged to different bands, and its signed change need not be negative. One may sum the inequality over disjoint time segments (each segment counts only its internal resource) but the resulting sum of the endpoint P terms also needs control. No such global charging estimate is claimed here.

## 4. Unconditional cluster bound for the selected-label stock

Return to the random CRT clock process, finite initial segment or infinite alphabet, through integer time U. Let Q>=ceil(sqrt(2U)), Delta>=0 integer. Restrict to selected labels in [Q,2U+1]; this includes all labels in a positive attained-peak prefix, since its POST-gain is <=2U. Define Cluster_(k,Q,Delta) to be existence of k+1 distinct selected labels in this range whose maximum minus minimum is <=Delta, with k>=1 fixed.

At each tick the exact conditional history law bounds the hazard of an unused p>=Q by 2/p^2. Therefore the expected number of first selections in [Q,2U+1] is O(U/(Q log Q)), by the elementary prime-count upper bound. Suppose a selected cluster exists and take its earliest first-selected member x. At that first-selection time x is known. Each of the other k cluster labels is selected for the first time later, lies within Delta of x and in [Q,2U+1]. Condition on the history including the selection of x. At each later tick, the probability of a fresh selection in this fixed interval of at most 2Delta+1 integers is <=2(2Delta+1)/Q^2, using the same conditional hazard. Expanding the kth factorial moment of the number of such later selections as in the preceding note, or union bounding k increasing ticks and iterating conditional expectations, gives a conditional upper bound (C U(Delta+1)/Q^2)^k/k! for the probability of at least k such labels. No independence of actual selected labels is assumed.

Sum this bound over all possible anchor first-selection ticks, weighting by their probabilities of being first selections in the band. This is legitimate since the bound conditional on the actual history through each anchor is uniform. We obtain
    Pr(Cluster_(k,Q,Delta))
       <= O(U/(Q log Q)) * [C U(Delta+1)/Q^2]^k/k!.
This is an existence bound for the entire selected stock, not just a short consecutive-return relation. It does not require that the clustered labels are selected near one another in time or that their first-selection-to-return spans are short. The factor Delta+1 uses a trivial count of integers rather than a short-interval prime distribution theorem.

Choose any fixed 1/2<theta<1, integer k with k(2theta-1)>1-theta, and 0<delta<2theta-1-(1-theta)/k. With
    Q=ceil(U^theta), Delta=floor(U^delta),
the right side is O_(k)(U^(1-theta+k(1+delta-2theta))/log U)=o(1).
The width is o(Q), so for fixed k the deterministic width restriction holds eventually for every P>=Q. On the complement of Cluster, every interval [P,P+Delta] with P>=Q contains at most k selected labels in [Q,2U+1]. Simultaneously for ALL such intervals and any contiguous segment of the gain-capped prefix (truncate before first POST-gain>2U), the conclusion of section3 holds. No need to union over the actual band choices or time segments, since the cluster exclusion already applies to the whole stock. In particular no band can contain C_k+1 events with intervening off-band gain <=P/4. This reaches scales arbitrarily close to the square-root threshold (fixed theta>1/2, k depending on theta); the bands become very narrow in relative width and C_k increases rapidly as theta approaches 1/2.

Example theta=2/3, k=2, delta=1/12: exponent 1/3+2(1+1/12-4/3)=-1/6. Thus with probability 1-O(U^(-1/6)/log U), all width-U^(1/12) bands above U^(2/3) contain at most two selected labels, and any ten band events in the capped prefix require intervening off-band gain >P/4. This controls mixed-scale return intervals even when arbitrarily many smaller events occur, unlike the previous short-support relation theorem. It does NOT imply that all such bands individually are visited for only a bounded total time. The deterministic resource alternative is essential.

## 5. Exact finite diagnostics

Saved research/min_ghost_narrow_band_mixed_gain_audit.mjs and research/min_ghost_narrow_band_mixed_gain_results.json with exact remote content readback at 345aa21ea461ee18e9fac03cfbe2f667927562ce. Sample independent common CRT coordinates with fixed seeds and finite prime alphabet <=4U, U=256,1024,4096,16384,65536; 128 samples per case except 64 at largest U. The earlier O(1/log U) coupling error is asymptotic, not a calibrated sample error.

For each selected prime P>=32 up to 2U+1 and k=1,2,3, take band width floor(P/(4(C_(k-1)+1))) (for k=1 use floor(P/4)), and skip the band if its actual full observed support exceeds k. Enumerate all subwords of band events with total off-band gain <=floor(P/4), verify length<=C_k, and verify whole observed band count <= C_k+(C_k+1) floor(D/(floor(P/4)+1)). Use the full observed path for these deterministic checks; gain-capped subwindows are also counted. At U65536: 4065 executed events,1754 subword checks (1708 ending at pre-gain<=2U),1408 whole-band resource checks; maximum observed length2. The code counts selected-stock clusters of size>1 in its diagnostic bands; it does not test the asymptotic cluster exclusion probability or the specific U^delta widths. No numerical estimate of its implied constant is claimed.

Independent exhaustive relaxed-word test: fix P, allowed labels, total off-band budget, enumerate all even increments between events and all possible signs on each label's first use. Thereafter its horizon coordinate is fixed. Explore until no further eligible extension, assert length<=C_k at every state. Cases (P,labels,budget): (41,[41],10), (41,[41,43],10), (101,[101,103],24), (1009,[1009,1013,1019],4). Recursion checks 2,160,222,432 states respectively, maximum lengths1,7,7,5. The relaxed examples do not assert actual clock attainability or optimality of C_k. The induction and cluster bound are paper proofs; no Lean compilation.

## 6. Remaining work

This removes the fixed LOW cutoff restriction from a class of bounded-support repeat-word estimates and gives a deterministic mixed-scale gain lower bound whenever narrow-band repeats persist. The selected-stock cluster estimate lets it apply uniformly to narrow bands at polynomial scales arbitrarily close to sqrt(U). The proof still lacks a global allocation of off-band gain and signed time costs across different bands, and does not bound widely separated label returns. The full repeat-bank convergence, eta->0, and the separate physical far-coalescence bound are unresolved. No main edit, no new branch, no twin-prime proof.
