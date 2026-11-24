# Reverse high-block ancestry: short height relation and source-weighted normalized-parent deletion

2026-11-24 JST. Continues f14c3539cfca100b0359b87003ca94f0d66b042b on the SAME research/min-cycle-forest-2026-11-24 branch. Elementary paper deductions, standard one-dimensional upper-bound sieve and exact finite audit. Not Lean-checked. The aggregate deep-ancestry estimate and twin-prime conjecture remain open.

## 1. Exact reverse high-block formula

Canonical MIN, original odd M in [X,2X), N=X/2, B=ceil(sqrt(7X)), original individual cutoffs K(M)=floor((7M-1)/4). LOW7, L=210. Use any source-preserving absorbed process on selected high keys, including the uniform cap T=B. Retain actual original cutoff tags. A current proposed high event at time n, pre-horizon C, selected p>7 is computed even if stopped before execution; its hypothetical post-height h'=2n-(C+p-1)>=0. If a tag has a preceding executed high event q>7 at time u, pre-horizon D, let h=2u-(D+q-1), and let g be the intervening even LOW-only gain, 0<=g<L. Then C=D+q-1+g and 0<n-u<=3L+2r(C), by the LOW barrier and actual next-clock bound. Write h=b+2kq, h'=b'+2k'p, where b,b' are respectively 0 or6 according to the two event parities and k,k'>=0. The exact identity is
    2kq = (2k'+1)p+e,
    e=b'-b-2(n-u)+g-1,
    |e|<=7L+4r(C)+7.
(The bound is intentionally loose; e is always odd and nonzero.) This holds for ALL depths and actual clock choices, including proposed stops. In addition q|D+/-1 and p|C+/-1. If q=p>L+3, those two divisibilities imply q divides the odd nonzero integer g-1+sigma_current-sigma_previous of absolute value <q, impossible.

For a current physical high event (n,p,C), enumerate even 0<=g<L and 1<=delta<=3L+2r(C). The preceding high post-state must be (u,H)=(n-delta,C-g). If u is even, its previous high label q divides both u and H, and if odd, both u-2 and H+2. Its nonreset height quotient J=(2u-H-b(u))/2 is a nonnegative integer for a possible q>7. If J>0, enumerate just the prime factors q>7 of J which also meet these clock and horizon conditions, then D=H-q+1. If J=0, enumerate the corresponding gcd factors instead (reset case). The actual low-only suffix and the actual MIN/stop/cutoff conditions must still be checked; this enumeration gives a complete candidate interface, not a claim all candidate paths are admissible. In particular, for a nonreset preceding state and q>=Y>7, the number of possible labels per (g,delta) is <=log(max(1,J))/log Y. The number of candidate labelled previous high keys for a short clock is O_L((1+r(C)) log(2X)/log Y), when all preceding states are nonreset. It can be sharpened by using the current h'+p+O_L(1+r) as the upper bound for J. For p>7L+4r(C)+7, a previous reset is impossible because k=0 would require (2k'+1)p=-e, impossible. A tag with NO previous high event cannot execute or propose such a large p at a short clock either, when p>6+6L+4r+1: its pre-height <=6+6L by the initial low prefix, so p-1<=h_pre+4r. These are local reverse constraints, not a uniform contraction of arbitrary reverse trees.

## 2. New full-source normalized-parent deletion, for ALL previous high prime sizes

Let alpha,beta,gamma,delta>0 be fixed with 2alpha+beta+gamma+delta<1. (Here delta is an exponent, unrelated to the time-offset variable in section1.) Put
    Q=ceil(B/log^alpha B),
    H0=ceil(B log^beta B),
    z=ceil(log^gamma B),
    W=log^delta B.
Call a transfer qualifying if the current proposed high event has p>=Q, r(C)<=z, hypothetical post-height h'<=H0, and the whole executed preceding high-key original-tag mass m(q,D)<=q W. No lower cutoff on q beyond q>7, no bound on depth, no bound on current group mass, and no restriction on whether current event resets. For all sufficiently large B, Q>7L+4z+7 and Q>L+3. Thus the tag has a preceding high event (by the preceding initial-prefix argument), k>=1, q!=p. The identity in section1 implies q divides the positive integer
    A=(2k'+1)p+e,
    1<=2k'+1<=1+H0/Q=O(log^(alpha+beta) B),
    |e|<=7L+4z+7=O_L(log^gamma B).
A is O(H0+B+z)=O(B log^beta B), since 2k'p<=H0. Even when counting all tuples with coefficient a=2k'+1 up to its common bound, A<=O(B log^(alpha+beta) B), which is sufficient for the divisor bounds below. All possible g and signs have O_L(1) choices.

For fixed distinct primes q,p, g and both signs, the congruences at D and C=D+q-1+g give O(1+X/(pq))=O(X/(pq)) possibilities for D. For each such fixed tuple, summing the number of qualifying tags over ALL arrival and event-clock times is at most m(q,D)<=q W, because each original tag can execute a particular previous key only once, and can propose the specified next key only once. This includes tags in an arbitrarily heavy stopped current key. Therefore an upper bound for the total qualifying tag INCIDENCES over the entire process is
    O_L(X W sum_{a,e} sum_{Q<=p<=B prime} (1/p)
                   #{prime q>7: q!=p, q|a p+e}).
The integer a is odd positive in the indicated range, e is odd and nonzero in the indicated range. Overcounting parity and possible k' is harmless. Notice the q-dependent mass cap has cancelled the 1/q from CRT. The remaining sum is a shifted-prime divisor sum, not a product of two unconstrained source masses.

We bound this sum for each FIXED a,e. For q>sqrt B, the integer ap+e=O(B polylog B) has at most two such distinct prime factors for all sufficiently large B (three would give >B^(3/2)). Thus their contribution is
    O(sum_{Q<=p<=B prime}1/p)=O(log log B/log B).
Use the standard elementary prime count and partial summation for this top-band harmonic bound.

For 7<q<=sqrt B with q not dividing a, divisibility forces one residue of p modulo q. If that residue is zero, there are no p!=q. Otherwise the standard dimension-one upper-bound sieve on this progression in [Q,B] gives O(B/(q log B)) primes, uniformly in q, a, e. For completeness: embed the variable interval in one of length comparable to B/q>=sqrt B; omit q, use one forbidden residue at each other prime up to B^c for a sufficiently small fixed c>0, with a standard small-power sieve level; the omitted factor is bounded, and the residue remainder is negligible. All p>=Q exceed the sieve cutoff. No prime-distribution lower bound is needed. Weighting by 1/p<=1/Q and summing q gives
    O((B/Q) log log B/log B).
For q|a, divisibility is possible only if q|e as well. There are O(log log B) possible distinct prime factors of a, since a=O(log^(alpha+beta) B), and for each the harmonic p sum is O(log log B/log B). This crude estimate is O((log log B)^2/log B), absorbed into the preceding bound because alpha>0. If a=1 there are no such factors. These estimates cover every q>7, including fixed small q. They prove uniformly per (a,e)
    sum_p (1/p) #{q>7: q!=p, q|ap+e}
        = O(log^alpha B log log B/log B).

There are O_L(log^(alpha+beta+gamma) B) choices of a,e. Hence the number of qualifying tag incidences, and therefore the number of DISTINCT original roots ever using such a transfer, is
    O_L(X log log B * log^(2alpha+beta+gamma+delta-1) B)=o(X).
For example alpha=beta=gamma=delta=1/8 gives O(X log log B/log^(3/8) B). This theorem applies to arbitrarily deep ancestral transfers, not just first saturation at a small fixed mass, and includes the whole original tag mass at the qualifying transition. It does not require distinct previous source sets at different times (we count incidences), or the two parents to be independent. No external literature search was performed; the same standard upper-bound sieve framework as the earlier arithmetic notes is used here in dimension one.

A simpler corollary avoiding even the dimension-one sieve: if q>=exp((log B)^theta), theta>0, each positive A has O(log^(1-theta) B) such prime factors. The above sum is bounded by that factor times the top harmonic p sum. This yields O(X log log B/log^(theta-alpha-beta-gamma-delta) B) when theta>alpha+beta+gamma+delta. For the stated exponents and theta=3/4 this is o(X). The full theorem above is stronger because it also includes small q.

## 3. Consequences for actual reverse ancestry and the remaining mass gap

In the uniform projected high-key stop process T=B, every executed predecessor has mass <B. With alpha=delta=1/8, q>=Q implies qW>=B. Thus ALL transfers from a preceding top label q>=Q to a current top p>=Q of small r and bounded post-height are included in the theorem, without any further mass condition or prior height condition. This removes o(X) distinct original roots over ALL depths, not just o(X) candidate keys. In particular for any remaining root, a cheap top event with post-height <=H0 must come from a previous high key with
    q<Q and m(q,D)>q log^(1/8) B.
The absence of a previous high event or a previous high reset is impossible for these cheap large-p events, as in section1. The strict lower bound on the previous mass is a new direct ancestry constraint. A previous root may still have passed reset states farther back. This does not claim that cheap top events represent a large fraction of all stops or travel.

A variable stopping rule can also impose m(q,D)<tau_q=ceil(q W) at EVERY high key. Its R_pre is o(X^2), since the earlier S_q=O(X/log^2 q) and LOW block cost bounds give
    R_pre <= O_L(X) + O(X W sum_{7<q<=B prime} q/log^2 q
                           + X L W pi(B))
           = O_L(X+X B^2 W/log^3 B+X B W/log B)=o(X^2)
for delta=1/8. For executed keys m<ceil(qW) implies m<=qW. Thus EVERY tag ever proposing a cheap top event of bounded post-height is covered by the normalized-parent deletion; in particular only o(X) tags stop at such events. The rest may stop at smaller labels, at large r, or at large height. This alternative rule has much smaller caps at small labels and does NOT imply a smaller total stopped population. It is an exact illustration of how the mass-normalized reverse estimate can interact with absorption.

For the original uniform cap, classify witness pairs from the stopped-cohort balanced blocks of size [T,2T-1]. Each root has at most 2T-2 possible witness partners, so all witness pairs involving any root deleted by the normalized-parent theorem total o(XT). This is valid for far or near pairs, regardless of where they first meet. It cannot be extended to all residual first contacts without an estimate on the superlinear normalized parent masses, high heights, expensive clocks or lower current labels. The theorem does not solve the all-pair bound. It supplies an actual source-weighted estimate in a particular reverse class and identifies the necessary overconcentration in the complementary cheap-top class. To finish the existing projected-stop proof still requires an aggregate bound on the residual far stopped-cohort witness pairs (<(1/2-epsilon)NT on unbounded windows). The normalized-mass obstruction m(q,D)/q>>1 for smaller q is now a concrete reverse target.

## 4. Exact finite audit

Saved research/min_reverse_cheap_top_transfer_audit.mjs and research/min_reverse_cheap_top_transfer_results.json, exact remote readback at f469d686114dd3cfe729ee01018c754824f8e433. Execute:
    node research/min_reverse_cheap_top_transfer_audit.mjs 256 1024 4096 16384 65536 262144

The function bodies were executed in the current runtime. Retain ALL original sources and individual cutoffs. Uniform caps floor(B/4) and B. Verify exact gain and elapsed bounds, both high-event height congruences, the linear identity, the error bound, A divisibility, same-prime exclusion when p>L+3, whole predecessor mass <T, actual tag incidences <= sum of whole earlier masses over distinct eligible tuples, and exact root conservation. Also verify per normalized tuple the actual whole predecessor mass <=qW. 10803 independent literal parity-GCD clock and terminal decisions at X256/1024 (798+1482+3865+4658). The first attempted in-memory run had an SPF overwrite error; it failed the literal check, was corrected, and only the corrected script and results were committed. Final R and stop counts match the preceding independent audits.

At X262144,B1355,N131072,T338: 11112 stops, 119960 genuine twin terminals, no bad terminal, R=98554147, 1108068 verified consecutive high-event relations. At T1355: no stops, all 131072 twin terminals, R=107745566, 1217087 verified relations. Four diagnostic modes use explicit finite Q,H,z,Y,W; the normalized count requires q>=Y, A>0, q!=p, and m<=qW. Some finite modes deliberately do not satisfy the large-B separation hypotheses (e.g. z can exceed Q or the conservative L term can dominate). They are finite classifications of actual transfers, not empirical proofs of the asymptotic estimate.

At X262144,T338:
| Q,H0,z,Y,W | normalized distinct tags | incidences from q<Q | distinct tuples | normalized-uncovered incidences with q>=Y and cheap bounded-height current top |
|---|---:|---:|---:|---:|
|678,2710,31,37,2|226|226|10|115|
|452,5420,31,11,2|759|613|32|1044|
|678,1355,7,11,1|68|68|2|232|

In the second mode, 146 original tags traverse 2 distinct cheap top-top tuples with both post-heights bounded by H0, all included in the normalized count. A representative transition: q521, p1061, D755970, C756492, g2, previous post-height1048, current post-height6, r23, k1,k'0, e=-19. Indeed 2*521=1061-19. The narrow asymptotic diagnostic mode at these finite sizes has z=2, so no eligible odd r; its zero counts are vacuous. The broader finite modes are for testing the actual formula and mass dependence. At T1355 in the second mode 1363 uncovered incidences remain versus 759 qualifying incidences. Thus it would be incorrect to assume every predecessor satisfies the normalized mass bound.

No new branch, no main edit, no Lean compilation, no claim of a completed proof.
