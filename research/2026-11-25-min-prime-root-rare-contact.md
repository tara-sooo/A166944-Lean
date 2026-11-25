# Rare compressed-contact supports and logarithmically weighted thin groups

2026-11-25 JST. Continuation of 5b545e4e74e4590870d8a16af372e297cf31a462 on research/min-prime-root-repeat-energy-2026-11-25. Combines its first projected contact ledger, the gain-stopped prime-root ensemble of a5e1119, the two-form sieve of 32d4185 and the rare-set reverse expansion of the parallel short-clock branch f83cb64cd8d8. New unconditional deletion of o(N) original prime roots and a separate whole-pair energy bound for one very large recent label against a thin group at ANY scale. Neither is a proof of the remaining energy or medium moment. Paper deductions and finite audits, no Lean compilation or novelty claim.

## 1. Compressed incoming histories at every scale

Keep X dyadic, B=ceil(sqrt(7X)), u=log B, l=log u, T=floor(X/u^(1/4)), N=#prime roots M in [X,2X), N~X/log X. The original canonical MIN prefix includes the first event crossing gain T or the original terminal/cutoff. Its full list of vertices includes the initial and final ones. Each root has total gain G_M<T+B and total r-cost at most 1.5 G_M. The first common horizon J of two roots charges their entire later ordered pair energy by at most 3 min(C_end(M)-J,C_end(M')-J)<=3(T+B), as in 5b545e4. This does not require equal physical times or a common future path.

Choose y maximal with L=2 product of odd primes <=y <= l^(1/4), for sufficiently large X. All maximal contiguous LOW blocks (p<=y) have gain <L. At a full vertex C let q be its last completed non-LOW label, and D the post-horizon of that selection. If no non-LOW has occurred use q=0,D=2M-2. Then 0<=C-D<L, even, and if q>0 we have q|D or q|(D+2). The compressed key is (D,q). At a first common projected horizon the two keys are necessarily different: if D<C the previous common D contradicts first contact; if D=C and q>0 the common predecessor D-q+1 contradicts it; if q=0 the initial horizon determines the root uniquely.

Work throughout in the even horizon domain V={2X-2<=C<=7X}, containing every original prefix vertex for sufficiently large X. Candidate non-LOW labels at D are odd primes y<q<=B dividing D or D+2, denoted P_y(D). They are an arithmetic relaxation, not a statement of actual MIN eligibility. The total distinct candidate log weight is <=log(D(D+2))=O(u). Their number is O(u/l), uniformly, since the product of m distinct primes is at least (m+1)! and log(D(D+2))=O(u). At C all relaxed compressed keys are obtained by even D in [C-L,C] with C-D<L, each with those candidate q plus a possible q=0. Thus the total number of possible keys is O(L u/l), including arbitrary small, medium or large last labels and root+LOW histories.

## 2. Rare arithmetic supports with two DISTINCT recent labels

For thresholds U,V0 let A(U,V0) be the set of C in V where there exist two distinct primes p>=U, q>=V0, both <=B, and even D,E with 0<=C-D,C-E<L, such that p divides D or D+2 and q divides E or E+2. Non-LOW restriction can only shrink the set. Offsets are drawn from O(L^2) possibilities and sides from four. For fixed p!=q and offsets/sides, CRT gives one residue mod pq. Since pq<=B^2=Theta(X), the count of C in the full interval is O(X/(pq)) (the usual additive 1 is absorbed). Hence
    |A(U,V0)| << X L^2 [sum_{U<=p<=B}1/p] [sum_{V0<=q<=B}1/q].   (1)
This is counting horizon support, not actual root pairs or tag masses.

For w>=1 and w=o(u), the elementary prime-count bound and partial summation give
    sum_{B exp(-w)<=p<=B}1/p = O((1+w)/u).
Set
    P=ceil(B exp(-u^(1/4))),
    Q=ceil(B/u), as in the preceding hybrid,
    V0=ceil(B exp(-sqrt(u))).
Eventually y<V0<P<Q<B. In particular P is much smaller than the previous B/u^(1/4), and V0 is still smaller. Define
    A_sym=A(P,P), A_asym=A(Q,V0).
Then (1) gives
    |A_sym| << X L^2/u^(3/2),
    |A_asym| << X L^2 (1+l)/u^(3/2).                       (2)
At a first contact involving two distinct compressed non-LOW labels, both >=P or one >=Q and the other >=V0, the horizon belongs to this union. No restriction on preceding word, root separation, or actual ancestor mass is needed. The asymmetric case genuinely extends beyond the symmetric one.

SAME-label exception: if the two compressed keys have the same q>=P but distinct D,E, one cannot count them as two prime moduli in (1). When q>L+2, both D,E are within L of C, and q divides one of each D,D+2 and E,E+2. Thus the only possibility is |D-E|=2 with the two divisibility sides different. Writing t_D,t_E for the two incoming q-event times, the earlier post-horizon uses the odd clock (t_D=q+2 mod 2q) and the later post-horizon the even clock (t_E=0 mod 2q), after swapping D,E if necessary. Their absolute time difference is >=q-2. Each subsequent LOW-only delay is <=3 times its gain <3L by wait<=2r<=2p<=3(p-1). Therefore the two actual times at C differ by at least q-2-3L. In particular such a first projected contact is asynchronous eventually. This does NOT prove a negligible contribution of the same-label class.

A second rare support A_rough consists of C for which neither C-1 nor C+1 has an odd prime divisor <=Z=floor(B^(1/4)). It includes twin terminal horizons. Apply the self-contained Selberg quadratic upper bound from 32d4185 to the two forms 2n-1,2n+1 on an interval of O(X) n values with z=floor(B^(1/8))<=Z. Every odd q<=z excludes two distinct residues, so the same proof applies (there is no exceptional odd coefficient divisor). It yields
    |A_rough| << X/u^2 + B^(3/4) << X/u^2.                (3)
This is a relaxation using small-factor absence only. In particular an actual nonterminal event with r(C)>Z belongs to A_rough.

## 3. Growing-depth reverse expansion, now small relative to PRIME roots

Let h=ceil(20 l), and A_deg={D in V: d_y(D)>h}, where d_y=|P_y|. As in f83cb64, since d_y(D)<=omega(D)+omega(D+2), and sum_{n<=7X+2}2^omega(n)<=sum tau(n)=O(X log X), we have
    |A_deg| << X u 2^(-h/2),
    D_edge:=sum_{D in A_deg}d_y(D) << X u^2 2^(-h/2) << X/u^4.
This uses only divisor counting, not statistics of actual paths.

For a set S subset V let Rev(S) contain all J-p+1 in V with J=C-e for C in S, even 0<=e<L, J in V, p in P_y(J). Distinct intermediate horizons are counted once. Thus
    |Rev(S)| <= g |S| + D_edge, g=max(2,hL).
Let A=A_sym union A_asym union A_rough union A_deg. Iterating the preceding inequality yields |Rev^j(A)|<=g^j(|A|+D_edge). A root which visits A after at most k completed non-LOW selections is in the union of the first k+1 reverse layers followed by one last LOW-offset expansion. This holds for repeated/interleaved labels as well: compress each actual LOW block to its true even gain <L, and use the actual candidate non-LOW predecessor relation. Thus the number of such ORIGINAL roots, even allowing composite initial candidates, is at most
    O(L g^k (|A|+D_edge)).
Unlike the parallel short-clock branch, we need o(N)=o(X/u), not merely o(X).

Choose
    k=floor(l/(4 log g)).
Then k->infinity and g^k<=u^(1/4). By (2)-(3) and the degree estimate, the number of flagged prime roots is at most
    O(X L^3 (1+l)/u^(5/4))=o(N).                       (4)
Indeed L<=l^(1/4), and every fixed power of l is o(u^(1/4)). Delete the ENTIRE original tag of any root flagged by visiting A within depth k. The total removed LINEAR r-cost is at most 1.5(T+B) times (4), hence o(NT). The actual selected weight of those full paths is bounded by the same amount. This is NOT a claim that their removed quadratic energy is o(T^2 B). It is valid to change the ensemble because the gain-crossing contradiction lower bound is per original root and there remain N-o(N) roots.

Consequences for surviving roots:
- At every visited vertex of depth <=k the horizon avoids all four rare sets. Hence a first projected contact between two surviving roots with the distinct compressed label conditions in section 2 must have BOTH histories of non-LOW depth >k. A single shallow side suffices to flag that root, regardless of the other side's ancestry mass. In fact any such exposed shallow root is deleted even without a second actual path.
- Every surviving vertex at depth <=k is not rough and so has r(C)<=Z, including a vertex at the original cutoff; it cannot be a twin terminal. There are O(L(k+1)) events through the first k+1 non-LOW hits, if present, since each LOW block has gain <L. Every pre-vertex of these events is at depth <=k and every wait is <=2Z. If fewer than k+1 non-LOW hits occurred, the same estimate would apply to the entire prefix. A gain crossing would be impossible, since gain<=6+2 elapsed=O(ZL(k+1))=o(B)<<T; an original cutoff without twins would also be impossible, since the final wait to the next eligible event is <=2Z and the required duration is Theta(X). Thus every surviving root completes its first k+1 non-LOW selections within elapsed time and gain O(Z L(k+1))=B^(1/4+o(1)). All selected primes through that prefix are <=1+this gain. This corollary is unconditional for sufficiently large X, using the original horizon invariant and cutoff. In particular no surviving root can select a label >=P or >=V0 in this first depth segment, even if the proposed large jump itself has a cheap clock. It does not bound later depth or first contacts between deep histories.

## 4. A weighted thin-group whole-pair bound at mixed scales

This is separate from rare-root deletion, and applies to arbitrary depths. Let
    Pstar=ceil(B/l^(1/8)), a=l^(1/8).
Say a vertex is super-recent if its compressed label p>=Pstar. (This cutoff is deliberately narrower than P or Q.) For a compressed key with q>0 define its thin cap
    b(q)=max(1,floor(a log q/l)); b(0)=1.
A group at C is thin if its actual original-tag mass is <=b(q). The masses may be taken before or after the new root deletion, consistently. The following bound holds for either choice. By section 1, the sum of b(q) over ALL possible compressed keys at a single horizon is
    O(L u/l + L a u/l)=O(L(1+a)u/l).                    (5)
Indeed the 1 parts use the distinct divisor count O(u/l), and the weighted parts use the total log divisor weight O(u). Thus (5) bounds the total mass of all thin groups, including arbitrary LOW/root+LOW and medium last labels. For q>=B^delta with any fixed delta>0, the individual cap grows at least on the order of u/l^(7/8), substantially larger than the old uniform thin threshold u^(1/4), but only with this narrower super-recent condition on the other side.

Each source has <=G_M/(Pstar-1) super-large selections. Each can supply at most L/2+1 subsequent super-recent vertex incidences, because only LOW steps follow until the next non-LOW label. Hence their total count is O(NT L/Pstar). At a first projected contact with one super-recent incidence and the other in any thin compressed group, charge to the super-recent incidence and use (5) for its possible partners. This counts first pairs at most
    O(NT L^2 (1+a)u/(Pstar l)).
By the remaining-gain pair budget, their ENTIRE ordered high energy (on any retained high-event subset) is at most
    E_super,thin << NT^2 L^2 (1+a)u/(Pstar l).
Since N=O(B^2/u), Pstar>=B/l^(1/8), a=l^(1/8), and L^2<=l^(1/2),
    E_super,thin/(T^2 B) << L^2 (1+a) l^(1/8)/l = O(l^(-1/4)).
Thus E_super,thin=o(T^2 B). This is a genuine energy deletion, unlike the root pruning in section 3. It removes some deep, mixed-scale first contacts where the previous recent-high/recent-high thin rule did not apply, including a super-recent group meeting a thin medium or root+LOW group. No restriction on the super-recent side's own ancestor mass or complexity. It does not control two thick groups; the narrower threshold on the super-recent side is essential to this estimate. The sum in (5) counts capacities, not actual occurrence probabilities.

## 5. Remaining hybrid criterion

Apply the previous accounting deletions to the original prefixes of the N-o(N) surviving roots. Their linear costs remain o(NT) by the previous uniform estimates (restricting an already proved selected/clock deletion to a subset cannot increase its cost; one may keep the original choices). The old medium Cauchy bound and LOW attachment still work with original N as upper bound. The previous near-pair, low-complexity, recent/small, recent/thin and root/recent first-contact energy estimates also apply to any subset of surviving roots. For thin groups one can retain their original definitions, or use the new smaller masses where the same proof applies.

Let E_newbad be the energy of pairs in the surviving ensemble which evade all the old exclusions and the new super/thin class. Then the surviving high energy equals E_newbad+o(T^2 B). It is NOT asserted equal to the high energy on all original roots up to that error: pruning removed tags may remove large pair energy. The residual includes:
- first contacts with distinct recent labels in A_sym or A_asym only when both non-LOW depths exceed k;
- same-label shifted recent keys (not covered by distinct-prime CRT);
- super-recent contacts with the other group thick in the label-dependent sense, or contacts without a super-recent side;
- other restrictions of 5b545e4 on surviving bad pairs.
A first contact outside A_sym/A_asym can still have shallow/deep histories unless excluded by another rule. The early-depth corollary is not a bound on the depth of an arbitrary residual contact.

On an unbounded common dyadic sequence, the still OPEN estimates
    Z_m=O(N B log^3 B), E_newbad=o(T^2 B)
for the surviving residual imply R_surv=o(NT), contradicting R_surv>=(N-o(N))(T-6)/4 in a twin-free window. The new steps are unconditional domain reductions, not a proof of those estimates. A possible next target is the actual thick-group cross product under the new capacities and minimum remaining gain budget, and same-label asynchronous lag classes.

## 6. Reproducible finite audit

Standalone ECMAScript research/min_prime_root_rare_contact_audit.mjs, exact remote readback at ab907803d113dbd0ce772a67ad19fb46e1e8e636, blob 29f110b86f3b2db76ad1342896dae6ced33ba353. Run:
    node research/min_prime_root_rare_contact_audit.mjs 256 1024 4096 16384 65536 262144
Executed the function in the available ECMAScript tool runtime, not a separate Node invocation. All 18 window/mode combinations passed. Literal parity-GCD comparisons at the two smallest windows: two1707, rough1183, gain1719, as in the earlier prefix audits. Explicitly constructs relaxed arithmetic degree/rough/symmetric/asymmetric exposure sets on the even interval, deduplicated reverse layers and LOW offsets; verifies layer edge bounds, every actual shallow flag's inclusion in the relaxed root union, retained shallow avoidance, actual LOW gain/time bounds, actual first-contact compressed key distinction, distinct-label support and one-sided shallow deletion, all thin capacities and whole-pair remaining gain bounds. Five same-label shifted first contacts satisfy the exact difference-two and time lag inequality (including repeats across test modes). Independently recomputes full high E before/after actual root pruning from horizon counts, and verifies the disjoint pair classes pruned, superThin, remaining using the ORIGINAL first projected contacts. All finite energy values safe integers. The audit tests the full high p>=Q set, not the entire earlier cumulative hybrid marks. It does not test the asymptotic early-depth corollary at the small parameter gates or the uniform analytic prime-sum and sieve estimates themselves.

Modes: two uses T=4B, P=ceil(B/3), Qasym=Pstar=ceil(B/2), V0=ceil(B/6) with small guards, marks only A_sym/A_asym/A_deg; rough uses T=B with these diagnostic thresholds but marks only A_rough/A_deg (Z=17); both use k=2, L=6,y=3, degree threshold8 and b(q)=max(1,floor(2 log q)). Gain uses asymptotic T,P,Qasym=Q,V0,Pstar,Z,h,k,b formulas with finite guards, but fixed L6,y3, and all four rare sets. Its k=0 at all tested X; the diagnostic modes exercise two actual reverse steps. The loose finite bounds on the rare sets and reverse unions can be large, as expected; no finite fraction is evidence for the asymptotic o(N) rate.

| X | two-mode prime roots | actual flagged roots | full high E before | full high E after root pruning |
|--:|--:|--:|--:|--:|
|256|43|38|9370|413|
|1024|137|107|17543|869|
|4096|464|327|304073|29345|
|16384|1612|970|2448963|345932|
|65536|5709|3100|23319896|4838968|
|262144|20390|9852|216308331|54343819|

At largest X=262144, B1355, two-mode T5420. A_sym88823, A_asym131073, union including exceptional143620, two exceptional degree vertices (18 candidate edges), reverse layer sizes143620,429496,608008; 20358 of 20390 roots in relaxed union versus 9852 actually flagged. 6463 have symmetric shallow exposure, 9128 asymmetric, overlap allowed. Actual removed clock8539691 of R16602377. Full first projected pairs366974; 582 distinct symmetric,133 shallow,0 shallow surviving; 469 distinct asymmetric,217 shallow,0 shallow surviving; 60 symmetric and54 asymmetric deep pairs survive (overlap allowed). Super-recent incidences6000 from4195 selections; 4891 independent super/thin first pairs of which4866 other label below P; 914 survive pruning in this class, ordered energy641840, diagonal of surviving high4688735, remaining pair energy49013244. Full high E after pruning54343819=4688735+641840+49013244. The large remaining energy is not bounded by the new class estimate.

Rough-mode largest: actual flagged12488, relaxed20366, shallow expensive high visits2885 (all their roots flagged); full E89384449 ->17255285, surviving super/thin energy80664, remaining pair14337772, diagonal2836849. Gain-mode largest: k0, all roots terminate at twins before T; actual flagged13249, relaxed16208, full high E220705320->29756235, remaining pair26295556. Analytic depth and root-fraction asymptotics not visible. No Lean compilation, no main or other branch change.
