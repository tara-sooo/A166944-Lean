# Exact reverse-clock ancestry and rough long-wait fibre budget

2026-11-24 JST. Continues a0f84a8b762a57d1ee2d2a3fea65b28afc5bb957. New paper deductions and finite audits, not Lean-checked. No proof of the twin-prime conjecture.

## 1. Exact reverse recurrence

Keep original canonical sources odd M in [X,2X), t0=M+2, C0=2M-2, K(M)=floor((7M-1)/4), B=ceil(sqrt(7X)), LOW7, L=210, P=pi(B)-4, m=2P, Q=ceil(B/log^(2/3) B). Count first min(m,actual high length) high selections. Let t,C be a candidate post-event state. The admissible incoming label p must satisfy:
- p odd prime <=B, p|C and t=0 mod 2p for even t; or p|(C+2) and t=p+2 mod 2p for odd t.
- With D=C-p+1, p is the least active prime at time t for pre-horizon D.
Write ell(t,D) for the last eligible clock time STRICTLY below t at D, over all primes in the pool (using the periodic extension to integer times, and intersecting with u>=X+3). Then the exact predecessor interval is ell<=u<t. This follows because the next event is the first strictly after u, not the first at or after u. In particular ell>=t-2p. Previous physical states are roots, or post-event states; for the latter their candidate times u can be enumerated from factors of D and D+2. Deduplicate times when constructing this union.

Fix the final query time T, restrict roots to K(M)>=T, and let F_T(t,C,k) count original sources reaching physical state (t,C) (root or post-event) with at most k high selections. It is the sum of the root indicator and
    sum over admissible incoming p, k>=1_(p>7)
      sum over allowable predecessor times u in [ell(t,D),t)
        F_T(u,D,k-1_(p>7)).
The root indicator is 1 exactly for t=M+2, C=2M-2, M in the odd source window, K(M)>=T. Horizon decreases on reverse edges. Distinct terms count disjoint original sources, since each source has a unique actual predecessor and never revisits a horizon. The final cutoff test at the root suffices for the whole reverse path, whose times increase toward T. Counting a prescribed high q event into (T,C) uses only its incoming term at k=m. Summing over its possible final times gives W(q,C) exactly. To count only events whose wait exceeds 2z, restrict that LAST predecessor interval by u<T-2z; earlier recurrence unchanged. This yields W_long(q,C). No arbitrary-state mixing assumption.

The time-free relaxation drops all time/clock/cutoff constraints and retains only reverse horizon edges D=C-p+1 with p dividing C or C+2, and the remaining high budget. Roots are the distinct reachable initial horizons. This is an upper bound, not an exact count. The audit exhibits severe overcounting.

## 2. New long-wait weighted criterion

Define z=floor(B^(1/4)), and call a LARGE (p>=Q) high selection LONG if its wait from the immediately preceding event (or original start) is >2z. Let H_s,H_l count small and large high selections, and R=sum over LONG large selections of p, all with original source weights. A is the small-label excess from the preceding note, so H_s<=A+o(XP).

For each source truncate at its last included high event (or its start if none). All earlier LOW-only blocks have elapsed time <3L; the sum over those blocks is <=3L(H_s+H_l). A small high event waits <=2Q, a short large one <=2z, a long large one <=2p. Initial deficit 2t0-C0=6 and invariant C<=2t bound the total LARGE gain by 6+2 elapsed time. Summing over N=X/2 sources gives the exact inequality
    (Q-1-6L-4z) H_l <= (4Q+6L) H_s + 4R + 6N.                 (1)
This does not require the no-twin hypothesis. Since Q grows faster than z, it implies
    H_s+H_l <= (5+o(1)) A + (4+o(1)) R/Q + o(XP).
All nontwin sources contribute m=2P high selections once the established strict clock prerequisite m(2B+3L)<3X/4-2 holds. Thus an upper bound strictly below XP suffices.

## 3. New sparse rough-key estimate

For a long large event at pre-horizon D, both D-1 and D+1 have no prime factor <=z. Indeed every such prime dividing a neighbor would give a clock within 2z, contradicting first hit. Let T_X contain the possible post-large keys (p,C) satisfying 2X<=D=C-p+1, C<7X, p>=Q, p|D+sigma for one sign sigma, and both neighbors z-rough. For fixed p and sign write D+sigma=p h. Then h and ph-2sigma have no prime factor <=z. For large B, p>=Q>z. For each odd prime ell<=z, exactly two distinct residues of h are forbidden; their determinant is the nonzero constant -2sigma. Ignore parity if desired. The h interval has length O(X/p) and lies inside an interval of length comparable to X/p (>=c B). The standard two-dimensional upper-bound sieve already used in research/2026-11-24-min-sieved-multidonor.md, section 2 (Ford, Sieve Methods, Theorem 2.4, https://ford126.web.illinois.edu/sieve2023.pdf), gives O(X/(p log^2 B)) candidates uniformly in p and sign. Indeed local density is 2/ell for odd ell<=z, remainder O(2^omega(d)), summed over d<=z is O(z log(2z))=o(B/log^2 B); the Mertens product is O(log^-2 B). Consequently
    sum_((p,C) in T_X) p = O(X pi(B)/log^2 B)=O(XB/log^3 B).
Let tau=floor(B log B), and define the weighted long-wait excess
    J_w = sum_(p,C) p (W_long(p,C)-tau)_+.
Then R<=tau sum_T p+J_w=O(X B^2/log^2 B)+J_w.
Dividing by Q gives
    R/Q <= J_w/Q + o(XP).
More generally any tau=B log^gamma B with gamma<4/3 works, because P~B/log B. Thus the OPEN sufficient condition is
    liminf_(dyadic X) [5 A + 4 J_w/Q]/(XP) < 1.                (2)
The asymptotic coefficient errors do not matter on a subsequence where the nonnegative normalized sum is bounded strictly below one. This route permits a larger per-fibre threshold than the previous B sqrt(log B), and only counts long-wait events; it has a weight p/Q and a larger small-side coefficient, so is an alternative, not a strict implication between the two sufficient conditions. Neither A nor the required weighted heavy tail is proved. The reverse recurrence gives an exact arithmetic representation of the new tail but no asymptotic bound on its own.

## 4. Actual finite tests

Python 3:
    python3 research/min_reverse_ancestry_audit.py 256 1024 4096 16384
All reached keys at X=256,1024, top 8 at X=4096,16384; 61 keys, 1889 possible final event times, including times not reached by actual sources. Both full and long-wait fibre counts match forward replay at every tested time. 6140 literal parity-GCD comparisons. Top key per window:
| X | p | C | W | relaxed roots | long W |
|--:|--:|--:|--:|--:|--:|
|256|23|1012|30|109|30|
|1024|67|2544|46|101|6|
|4096|73|15474|72|1722|72|
|16384|149|64366|138|7579|138|
Max relaxed/actual ratio among tested keys was 353 at X=1024. Tested Python blob b661123a2ce3e24099238e894dfe9f8d552f1bb1, readback at 8ad53829989460dab84cd8783710a854f1ffad90.

C++17:
    g++ -std=c++17 -O3 -Wall -Wextra -Werror research/min_rough_fibre_audit.cpp -o /tmp/min_rough_fibre_audit
    /tmp/min_rough_fibre_audit 256 1024 4096 16384 65536 262144 1048576 4194304
Checks long roughness, actual per-source elapsed/gain accounting, inequality (1), and weighted excess bound with exactly enumerated relaxed T_X. All pass. Tested blob 05e96c6b57cb12b88780c13e90d8a24da4014bf0, readback at 18efdb6abca028597d09cad5f54f6029ddf3815c.

| X | z | long large count | max W_long | tau | J_w |
|--:|--:|--:|--:|--:|--:|
|256|2|120|30|161|0|
|1024|3|131|22|377|0|
|4096|3|1419|72|873|0|
|16384|4|4636|138|1975|0|
|65536|5|20692|286|4419|0|
|262144|6|83304|629|9771|0|
|1048576|7|305292|1195|21421|0|
|4194304|8|1182036|1494|46590|0|

Largest window: H_s=30364165, H_l=1199472, R=2823365774, A=2422567, 24530 observed long keys vs 536898 relaxed rough keys. Sum_T p=1515664706. Finite sieve asymptotic constants are not estimated; z is still small, and the strict clock prerequisite is not met at these scales. These diagnostics do not prove (2). Main untouched, no new Lean compilation. Next task: use the exact inverse clock intervals to bound original root mass on rough long keys, not the time-free ancestor graph, and separately control small excess A.
