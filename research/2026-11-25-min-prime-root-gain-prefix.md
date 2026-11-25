# Gain-stopped hybrid, relative rough-clock sieve, and scale-wise label concentration removal

2026-11-25 JST. Continuation of 32d4185300364b3e4440ea76d095b8106208180b on research/min-prime-root-repeat-energy-2026-11-25. Paper deductions on the actual MIN dynamics. In particular this changes the ensemble on which the previous hybrid targets need to be proved, while preserving the canonical clock and individual original cutoffs. It does not solve the remaining arithmetic estimates. No Lean compilation, no novelty claim, twin-prime infinitude OPEN.

## 1. A gain-stopped prefix suffices

Keep the usual prime roots M in [X,2X), N=#roots, B=ceil(sqrt(7X)), original s=M+2, C0=2M-2, cutoff K(M)=floor((7M-1)/4). The selected prime p raises C by p-1; each actual event wait is <=2r(C), where r(C) is the least eligible odd prime <=B. The pre/post horizon invariant C<=2t holds, with initial deficit 2s-C0=6. Each event's gain interval has length p-1, r<=p<=1.5(p-1), so selected-prime weight and clock cost are at most 1.5 times total gain.

Choose a gain threshold T with B=o(T), T=o(X). Run each ORIGINAL trajectory until the first event whose POST-gain is >=T, or its original terminal/cutoff, whichever comes first. Include the crossing event. Denote the resulting gain G_M and total minimum-clock cost R_M, and their sums G and R. This is a prefix of the original process, not a new dynamics or shortened time cutoff. Every pre-gain is <T and every G_M<T+B.

If a root crosses T, the horizon invariant at that post-event gives
    2(t-s)>=G_M-6>=T-6.
Since elapsed time through that event is <=2R_M, necessarily
    4R_M>=T-6.
If a root does NOT cross and terminates without twins, its last quiet tail up to K(M) is <=2B: a non-twin horizon in the original range has a least eligible prime <=B. Consequently
    K(M)-s<=2R_M+2B<=3G_M+2B<3T+2B.
But min_M(K(M)-s)=(3/4+o(1))X, so this is impossible for the chosen T eventually. Thus on a window containing no twin terminal, EVERY prime root crosses T and
    R >= N(T-6)/4.
An exact finite certificate whenever 3T+2B<=min_M(K(M)-s) and T>6 is
    4R < N(T-6).
Even without the first inequality, the number of crossing roots is at most 4R/(T-6); direct checking of the noncrossing cutoff condition distinguishes twins. For sufficiently large X with the first inequality, at least N-floor(4R/(T-6)) roots must terminate at twins. These are roots, not distinct twin pairs. Terminal horizons remain >=2X-2 and grow with X.

It follows that R=o(NT) on an unbounded sequence of dyadic windows suffices for twin-prime infinitude. No estimate of the remainder of any trajectory after the gain crossing is required.

## 2. Transfer of the preceding hybrid deletions to T=X/log^(1/4) B

Choose T=floor(X/(log B)^(1/4)). Then T/B->infinity, T/X->0, and log T~log X. For each fixed pre-horizon C, all its visiting original roots in the truncated ensemble satisfy
    C-T < 2M-2 <= C.
Their M values lie in an interval of length T/2. The uniform upper bound for primes in an interval (as used in 6d2f6bf9) gives O(T/log T) such roots. Each original root visits a pre-horizon at most once. This is a deterministic localization of original tags, not independence or an assumption about merger multiplicities. In particular two roots visiting a common pre-horizon satisfy |M-M'|<T/2. This remains true after arbitrary accounting deletions.

Here is the complete scale check for transporting the earlier selected-weight deletion constructions. Write l=loglog B, Q=ceil(B/log B), k=floor(sqrt(log B)). Use the same global B, prime ranges and full-horizon relaxed support sets from the earlier papers.
- First k occurrences per root-label cost at most N k sum_{p<=B} p = O(NX/sqrt(log B)) = O(NT/log^(1/4) B).
- The actual light-background endpoints have possible (C,p) selected-weight support O(X l^2/sqrt(log B)) from dc1b7e5. Multiplying by the localized tag cap O(T/log T), rather than N, yields O(NT l^2/sqrt(log B)). The separate relaxed light-horizon deletion, which was only an r-weight bound, gives the same order of r-cost and O(NT l^2/sqrt(log B)) deleted incidences. Do not use the extra relaxed horizon incidences as selected-weight seeds.
- The dense-word anchor support from edffc245 has selected weight X (log B)^(-1+o(1)). Each chosen anchor (C,p) carries at most O(T/log T) original tags, and the same per-source disjoint gain-interval cover costs at most 6K_d per anchor. Thus actual dense-word union weight is O(NT (log B)^(-1+o(1))). The dense words and anchors may simply be recomputed within each truncated prefix; all local hypotheses are unchanged.
- Total prefix gain is O(NT), so the two long-return deletions of dc1b7e5, with H0=ceil(B/sqrt(log B)) and F=ceil(l^2), cost O(NT/sqrt(log B)) and O(NT/l), respectively.
- For the inverse-square adaptive baseline REPLACE the old A=B^2/l^2 by A_T=floor(T/l^2) in k_p=k+floor(A_T/p^2). The selected-weight sum of the extra occurrences is O(NT/l) by the same reciprocal-prime sum. This is a new choice, not a transfer of the old larger baseline.

The FAST seed of dc1b7e5 therefore costs O(NT/log^(1/4) B) (the l^2/log^(1/2) term is smaller eventually). Use the same short/comparable parameters K,D and the same growing round counts t_A,t_B as that note: the A multiplier is at most log^(1/8) B, leaving O(NT/log^(1/8) B)=o(NT/l); after adding local long and the rescaled adaptive caps the SLOW seed costs O(NT/l). The B multiplier is at most l^(1/4), leaving O(NT/l^(3/4)). The gain halos and same-label dilation of 11104dc have purely source-wise weight multipliers unchanged, so the final selected-weight seed costs O(NT/l^(3/8)). All these sets are computed on the original truncated lists, before accounting deletion; future events past the threshold play no role.

The growing LOW primorial L<=(loglog B)^(1/4) has the same contiguous-block gain barrier. Its additional attachment cost for the selected-weight deletions is O(NT/l^(1/8))=o(NT). The separate relaxed-horizon count times L is o(NT). All high p>=Q hits number O(NT/Q). The initial blocks contribute O(NL). The old medium Cauchy coefficient sum O(Q^3/log Q) is unchanged. Thus LOW absorption and all these previous deletions continue to work. The quotient-block deletion of 32d4185 also works: its initial partial b-block cost O(N b X/log B)=o(NT), b=floor(log^(1/4) B); full block cheap-clock bounds multiply total selected weight O(NT), and their LOW attachment cost for p>=Y=ceil(l) is O(LNT/Y)=o(NT).

## 3. Two-sided gain trimming, not an energy estimate for the deleted portion

Let D0=o(T), D0>=B eventually, for example D0=floor(T/l). Delete all events with PRE-gain <D0, and all with distance from their POST-gain to the end of the truncated trajectory <D0. Their gain intervals are contained in the first and last D0+B units of that trajectory's gain. Therefore their combined selected weight is <=3(D0+B) per root. This proves a direct clock deletion of O(N(D0+B))=o(NT), plus LOW attachment O(NT/Y*L) if restricted to p>=Y; for all p>y one may alternatively account for LOW itself inside these two intervals, with at most two truncated LOW boundary blocks of cost O(L) per root. More explicitly, if performing the previous LOW absorption on the full prefix, each deleted p>y event inside the two trimmed parts can be charged the adjacent LOW block inside the same part, except at most two boundary blocks per root. All such LOW blocks have total gain <=2(D0+B+L); their clock cost is O(N(D0+B+L)). No multiplication by L of the entire trim count is needed.

A simpler scale check for the general hybrid is to choose D0=floor(T/l) as above: since count<=selected weight/3, even charging L to every trimmed event costs O(LN(D0+B))=o(NT). This is the choice used below and avoids any boundary bookkeeping.

The previous near-origin energy comparison (difference E_full-E_late) used radius B log^(2-epsilon) B, and required a quadratic bound on the deleted pair terms. Here only the deleted LINEAR clock budget is needed. We can remove the first and last T/l gain, which is asymptotically much larger than that radius. No assertion that the quadratic energy of the discarded events is o(T^2 B). In fact, even in the original full-horizon version, any o(X) gain prefix or suffix can be removed in this way at o(XN) clock cost. This is a distinct use of the old elementary gain inequality.

## 4. Relative clock deletion and a stronger uniform per-label sieve bound

Set Y=ceil(l) (for large B), and f(p)=sqrt(log p) for p>=Y. Delete every p>=Y event with r(C)<=p/f(p). This costs at most
    sum_deleted r <= 1/sqrt(log Y) * sum_all p
                  = O(NT/sqrt(log Y))=o(NT).
It is a clock deletion only, not necessarily small selected weight. Its extra LOW attachment is O(LNT/Y)=o(NT), since all p>=Y events have count O(NT/Y).

For a retained expensive hit of p>=Y use the earlier exact odd quotient coordinate (C+sigma)/p=2n+1. For ANY interval of H consecutive n values, choose z=floor(min(p,H)^(1/8)), with bounded min handled by an enlarged absolute constant. For sufficiently large p and min(p,H), z<=p/f(p)<r(C), z<p. The two linear forms of 32d4185 must both avoid odd primes <=z. The earlier self-contained Selberg bound, summing over both signs, gives
    number of retained p hits in this quotient interval
       << H/log^2(2+min(p,H)).
Indeed z^6<=H^(3/4), which is absorbed by the displayed main term uniformly. Distinct actual p hits of one source have strictly increasing n. This is a deterministic interval capacity bound, not an assumption that the hits sample the sifted lattice uniformly.

On the entire truncated source, its p-quotients lie in an interval of length <=T/(2p)+O(1). Enlarge to a full interval of length ceil(T/(2p))+3. Alternatively use z=floor(p^(1/8)) in that interval, with z^6<=p^(3/4). Since p<=B and T~X/log^(1/4) B, uniformly
    p^(3/4) = o(T/(p log^2 p)).
It follows that
    n_rel(M,p) <= C T/(p log^2 p)  for every p>=Y,
where n_rel counts all relative-expensive hits (or any subset). This improves the previous block-based bound O(X/[p(log z_p)^(3/2)]) to a full log^2 p denominator and the smaller gain scale T. It also supplies an upper bound for any subinterval of a long clean episode, with the local log(min(p,H)) scale. It does not require individual return gaps to be short or large, or restriction on the intervening donors.

For any P>=Y, the per-source moment in p>=P satisfies
    sum_{p>=P} n_rel(M,p)^2
       <= (max_{p>=P} n_rel(M,p)/p) sum_p p n_rel(M,p)
       << T^2/(P^2 log^2 P).
The weighted first-moment version is
    sum_{p>=Y} n_rel(M,p)^2
       << T sum_{p>=Y} n_rel(M,p)/(p log^2 p).
These may also be applied to the smaller final residual. Neither alone reaches the required aggregate medium moment; the low and intermediate p range still needs arithmetic control.

## 5. New scale-wise removal of concentrated repeated labels

The same pointwise bound allows a new selected-weight deletion, unlike the relative cheap clock deletion. Divide p>=Y into logarithmic bands
    2^j <= log p < 2^(j+1)
(start with the possibly partial band containing Y). In each source and each such band mark all retained relative-expensive hits of ANY at most a_j=floor(2^(3j/2)) distinct labels. For a canonical choice use the labels with largest remaining selected weight p n_rel(M,p), breaking ties by p. The cost of every marked label is <=C T/log^2 p. Thus the full selected weight of these marks, even with the label choices adapted to every original trajectory, is at most
    C NT sum_{j>=floor(log_2 log Y)} 2^(-j/2)
       = O(NT/sqrt(log Y))=o(NT).
No product of CRT moduli for these chosen label sets is required. The extra LOW charge can use the same O(LNT/Y) bound as in section 4.

More generally any prescribed a_j with tail sum sum a_j/2^(2j)=o(1) works; this choice permits approximately (log p)^(3/2) distinct labels per source per logarithmic scale. Entire concentrated expensive-label families with at most that many labels in each band are deleted. A nonempty surviving band must have had >a_j distinct expensive labels before this rank deletion. If ranks are chosen by selected weight, every retained label also satisfies a_j times its weight <= weight of the a_j deleted labels. This is a genuine concentration exclusion, but does not bound the number of labels actually present, or assert that locally dense words follow from this global abundance.

This rank deletion may be performed after the previous deletions and two-sided trimming. It counts ONLY relative-expensive incidences, so the selected-weight upper bound holds. Cheap selected labels must not be added to the rank weight or treated as already having small selected weight.

## 6. New sufficient conditions, and comparison with the full-window route

On this truncated ensemble after all these deletions, let n_m(M,p) count residual y<p<Q hits, and W_h(C) count residual p>=Q original source incidences. Then
    Z_m=sum_{M,y<p<Q} n_m(M,p)^2,
    E_h=sum_C r(C) W_h(C)^2.
The retained small/medium cost and LOW attachment are still controlled by sqrt(N O(Q^3/log Q) Z_m). Thus the previous bound Z_m=O(N B log^3 B) suffices: this term is O(NX/sqrt(log B))=o(NT). A more precise sufficient scale is Z_m=o(N T^2 log Q/Q^3).

For high cost use the old full-horizon support S0=O(XB/log^2 B) and Cauchy. Since N~X/log X and B^2=Theta(X), the sufficient energy bound is now
    E_h=o(T^2 B).
Indeed sqrt(S0 E_h)=o(NT). All deletions above have total cost o(NT), including the LOW charge, so these two joint OPEN conditions along the SAME unbounded dyadic windows contradict R>=N(T-6)/4. The high energy now only involves pre-gain <T, with a further trim of both ends, a relative expensive clock, and a nontrivial label-rank condition. In particular no pair with |M-M'|>=T/2 can contribute at the same C. T^2 B is smaller than the old X^2 B target; this is a different sufficient condition on a smaller domain, not a claim of dominance for arbitrary incidence families. The old full-horizon hybrid remains available. The parallel short-clock branch uses a different truncation (relative time of order B), not this gain cutoff.

For an exact finite diagnosis of the new deletion alone one can use the measured deleted r-cost and the residual moments in the same Cauchy inequalities, without invoking any asymptotic saving. The upper bound on R does not establish the two open estimates, and the finite occurrence of twins does not establish their limiting behavior.

## 7. Reproducible finite checks

Standalone ECMAScript research/min_prime_root_gain_prefix_audit.mjs, first exact remote readback at 03deef2172f2d19b00f42bd8c5c4212c894fd29b, blob 13df7085872948e0d121f7913bf2b2d07e35f646. Run:
    node research/min_prime_root_gain_prefix_audit.mjs 256 1024 4096 16384 65536 262144
Executed the function in the ECMAScript tool runtime (not a separate Node executable). Three modes x six windows. Exact prime-root MIN clock through original cutoff or first post-gain crossing; actual quotient identity, monotonicity and r bound; literal parity-GCD cross-check at two smallest windows. All crossing cost inequalities and noncrossing nontwin cutoff inequalities, gain cap, two-sided trim cost, exact actual roughness tests (q<=min(7,p-1,floor(p/f))), CRT period and quotient capacity, rank ordering bound, disjoint clock partition, original source pair separation and BigInt horizon energies checked. The prior Selberg quadratic oracle remains in 32d4185; this audit tests the integer arithmetic and structural changes, not limiting constants or the entire accumulated hybrid marking.

Modes: gain uses T=floor(X/log^(1/4) B), D0=floor(T/max(4,l)), f=sqrt(log p), Y=max(5,ceil(l)), growing band rank cap with finite guard. At tested scales almost all roots terminate before this T, and most costs are swallowed by the finite trim, so no meaningful test of the hard asymptotic residual. X256 has one noncrossing non-twin (3T+2B exceeds minimum cutoff duration there); the exact cutoff inequality passes, as intended. Short/four diagnostics use T=B or 4B, D0=floor(T/8) with min1, Y=7, f=2 and one label removed per band per root. They deliberately exercise nonempty crossing sets and residual energies, without claiming the asymptotic deletion budgets of sections 2-5 at those finite settings.

| X | T=B crossing roots | T=B twin terminals before crossing | T=B original prefix R | T=B retained high energy after trim/ratio/rank |
|--:|--:|--:|--:|--:|
|256|24|19|1578|13|
|1024|47|90|6712|23|
|4096|195|269|49962|333|
|16384|559|1053|296741|7757|
|65536|1740|3969|1959336|106309|
|262144|4992|15398|12402927|1000767|

At X262144, B=1355,N=20390. Short prefix events=464179; gain=14131702; min crossing clock=463, crossing clock total6611682; trim clock8561778, relative cheap131796, rank clock2311482, residual small354026, medium864370, high179475. 209565 roughness checks, 135273 exact quotient capacity checks, 24085 rank checks. Full high energy89384449, after trim14361769, after relative cheap14161751, after rank1000767. Remaining high hits735, max source mass16, max root separation460 (<T/2). T=4B has 170 crossing roots, 20220 twin terminals, total prefix R16602377, 612685 events; high energy216308331 ->39048530 ->37081283 ->12855195; retained high hits2289, maximum source separation1966 (<T/2). These counts include original tags and are not unique twin counts. Finite gain mode at largest X: all 20390 roots terminate at twins before crossing, R16687054 matches original full runs. All 18 audits pass. Literal comparisons: gain1719, short1183, four1707 across the two smallest windows. These tests do not establish the asymptotic sieve bound or the joint residual criteria.

## 8. Next target

Focus on the actual source multiplicity for the shorter gain-stopped ensemble: all contributors to a common horizon start within T/2, and the high residual has expensive clock and many active labels in its logarithmic band. The local interval capacity of section 4 constrains clean medium episodes. One next direction is to exploit this capacity with reverse p-deleted shadow or source-pair estimates for repeated rough quotient hits, instead of relying on a full-horizon mixture. No proof of the remaining medium moment or high energy; no main or other branch change.
