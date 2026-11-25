# Rough-slot inverse low tails and weighted incoming-anchor gain transfer

2026-11-25 JST. Continues ff58097eb153ad82484b0360a579cc265f735c8e (common-cell slots). New paper deductions: unique deterministic rough target after the last nonLOW event, negligible linear deletion of root-only low histories and thin comparable anchors by a weighted arithmetic sieve, and conditional transport of ALL same-slot comparable-anchor products to an upstream selected-gain energy. This includes cross products between distinct labeled anchors; it is not a proof of the upstream bound. No Lean compilation; twin infinitude remains open.

## 1. Actual low suffix and the unique rough target

Keep original dyadic X,N=X/2 odd roots M in [X,2X), B=ceil(sqrt(7X)), s_M=M+2,C0=2M-2,K=floor((7M-1)/4), H=4B,a=2B,u=log B,D=max(1,floor(B/u^2)). Work eventually with H+2B<=K-s_M for every original root. The natural occupations are late HIGH clipped to relative [a,H), or full completed positive-drift waits starting before relative H. All these waits finish by relative H+2B. Each nonterminal wait at C has outgoing selected p<=B and length <=2r(C)<=2p<=3(p-1); C<=2t, C strictly increases at events. The paper deductions work for arbitrary smaller nonnegative per-tag weights w_M(C)<=1. Use original unmasked histories and natural starts for ancestor labels.

Define rough if r(C)>=D/4 (and r(C)>0). Choose alpha=lambda=1/16, L the largest even primorial <=u^lambda, and y its largest prime, so L>=2 eventually, L->infty, L<=u^lambda and y=O(log u). The finite audits use fallback L=2 when the asymptotic bound is below 2; stress L=30,y=5. Eventually y<D/4.

For an original tag's entry into a rough horizon C at clock b, choose its latest earlier actual event with selected prime q>y, including an event ending at b itself. Its labeled physical post-anchor is A=(J,t,q), with J even, t<=b, q>y. If there is no such event, use its canonical root as the origin instead. Every intervening selected event is LOW (p<=y). The even-primorial barrier gives
    0<=C-J<L,   0<=b-t<=3(C-J)<3L.                     (1)
For a root-only origin substitute J=C0,t=s_M. Proof of barrier: each even multiple of L is an impassable upper barrier for LOW jumps. A selected p<=y cannot jump across that multiple: among even pre-horizons within p-1 of the multiple, the only eligible residue that can reach or pass it lands exactly on it. No LOW event can leave the multiple, whose neighbors are coprime to all p<=y. The sum of completed LOW wait lengths is <=3 times their gain; no extra clock overshoot is used in (1).

Starting at A, the deterministic low suffix ends at the first selected event >y, a twin terminal, or prefix cutoff. Since r(C)>y, the next event at C must be >y. Thus there is at most ONE rough horizon and clock slot (C,v), v its next event time, associated to this anchor over all original tags using it as their last nonLOW anchor at a rough wait. All longer actual continuations from the same state agree; an earlier tag cutoff only omits the target. This uniqueness includes the case J=C. It is stronger than merely bounding the number of rough horizons in the length-L interval. Multiple incoming labels at a single physical state are counted separately, not merged into a synthetic label.

Let n_A be the number of original source tags actually visiting labeled A as an event in their prefixes before relative H. Each root visits any fixed labeled A at most once. Let W_A(C) be the sum of the chosen occupation weights assigned to A at its unique rough target. Then 0<=W_A<=n_A. For each tag total anchor gain is O(B), so sum_A q n_A=O(XB). The associated quadratic gain G_A=q n_A^2 does NOT inherit that linear bound.

## 2. Unconditional low-root deletion

A root-only tag at C satisfies C-(2M-2)<L. The original root horizon determines M injectively, so at most O(L) such tags per rough horizon. The dimension-two upper sieve for C-1,C+1, with no odd prime factors <=B^(1/64) eventually, bounds the number of possible rough C in the natural O(X) horizon range by O(X/u^2). This is the same uniform two-form sieve as in min-clock-true-birth and earlier rough sieve notes. Hence all root-only rough occupations can be removed at linear cost
    R_root <= O(B L X/u^2)=o(XB).                     (2)
All their pair products disappear from the RETAINED energy definition, but the removed quadratic mass need not be o(XB u^3). No tag must be restarted, nor is this a deletion of all its subsequent occupations. Only the chosen rough visit weight is removed.

## 3. Weighted rough-anchor support and thin comparable peeling

Call a labeled anchor comparable at its unique rough target if q>=r(C)/u^alpha. Thus q>=c B/u^(2+alpha), so q is eventually above B^(1/64). It is crucial to sum candidate weights r(C), rather than replacing all of them by B.

Write e=C-J in [0,L), even. With parity k=t mod 2 the incoming event implies
    q | J+2k,  t=0 mod 2q (k=0) or q+2 mod 2q (k=1),
    d=2t-J=6k+2qj, 0<=d<=2H+6.
For each q,k there are O(1+B/q)=O(B/q) possible phase integers j. These bounds include reset d=6k; no nonzero divisor assumption is made. The exact finite phase condition allows j=-1 at odd selected q=3,d=0, not possible in the eventual comparable large-q band. The first diagnostic detected that special case and was corrected before the final runs.

For each q,k,e, the congruence C=e-2k mod q and the rough sieve give O(X/(q u^2)) possible C. Indeed C=e-2k+qz, and C-1,C+1 are two distinct forbidden residues modulo every odd prime <=B^(1/64) (q above that limit); interval length O(X/q)>=cB absorbs the uniform sieve error in the prior notes. Ignore additional parity and actual MIN restrictions for an upper envelope. For each actual A its target is unique; overcounting potential C or e only increases this nonnegative support bound.

Weight every comparable candidate (C,A) by r(C)<=q u^alpha. Summing over primes q from cB/u^(2+alpha) to B yields
    S_comp=sum_candidates r(C)
       <= O(X B L u^alpha/u^2 * sum_q 1/q)
       = O(XB L u^alpha log u/u^3).                  (3)
The final reciprocal sum is O(log u/u) by dyadic summation of the elementary Chebyshev prime-count bound over O(log u) dyadic bands, all log q asymptotic to u. No prime number theorem in short intervals is required. This is a weighted count of relaxed physical anchor-target keys, not a count of original tags.

Set m=u^(11/4). Delete the entire chosen occupation of every comparable anchor with actual unmasked n_A<=m. By W_A<=n_A and (3),
    R_comp,thin <= m S_comp
       = O(XB log u/u^(1/8)) = o(XB).                (4)
Since lambda+alpha+11/4-3=-1/8, the bound is strict. This removes all its incident retained pair products, including those with unrelated anchors or different clock slots; it is a LINEAR mask and not an absolute quadratic estimate. The cap is on actual source multiplicity, not on the number of distinct predecessor states. Remaining comparable anchors are genuinely thick n_A>u^2.75. Apply these masks before the final fixed-reference density gate in ff58097e, or reapply that gate. They are valid independently of earlier holes. The masks need not preserve natural MED destination budget.

An optional generalization (paper deduction only, not separately tested): for any fixed A0>0 use all anchors with q>=B/u^A0, not only comparable. Weight relaxed support by q instead of r(C), giving
    sum_candidates q=O(XB L log u/u^3).
Delete actual groups satisfying r(C)n_A/q<=m; their total linear loss <=m sum_candidates q=O(XB L log u/u^(1/4))=o(XB).
This adaptive rule extends to a smaller q/r ratio when actual n is sufficiently small, and a larger cap when q>r. No assertion that the adaptive rule handles all small-q anchors. It can be combined with (4) using disjoint priorities or simply a union bound on linear losses.

## 4. ALL comparable same-slot products transfer to selected-gain energy

Recall the exact slot classification in ff58097e: a slot at C is the next event time v; waits in one slot overlap, and OLD products occur only in same slots. For all comparable anchors whose unique target is the same slot (C,v), (1) and b>=v-2r(C) show
    J=C-e, 0<=e<L,
    v-2r(C)-3L <= t <= v-1.
For fixed e and side, q divides J+2k. Since q>=c B/u^(2+alpha), there are O(1) such large prime factors (the product is bounded by O(X)). For each q the arrival phase is a single progression of step 2q, giving O(1+r/q+L/q)=O(u^alpha) candidate times. Thus the number K_(C,v) of comparable anchor keys in a slot is bounded by O(L u^alpha). This is a local degree estimate, including reset or nonreset labels and every LOW suffix length, with no assumption on n_A.

Let W_comp(C,v)=sum of retained W_A over comparable groups in that slot. By Cauchy and r<=u^alpha q,
    r W_comp(C,v)^2
       <= K_(C,v) sum_A r W_A^2
       <= K_(C,v) u^alpha sum_A q n_A^2.
Summing over rough slots uses the UNIQUE rough target property, so each labeled A occurs at most once. For the actual thick comparable anchors that support retained occupation,
    E_rough,same-slot,comp-comp
       <= O(L u^(2alpha)) G_rough,comp
       <= O(u^(3/16)) G_rough,comp,                 (5)
    G_rough,comp=sum_A q n_A^2.
The left includes diagonals and cross products between DISTINCT anchors within one clock slot, therefore also bounds the OLD subset. It is an exact conditional transport of upstream gain energy, not an unconditional payment. No factor equal to the number of rough clock slots is needed. A sufficient upstream bound for this sector is G_rough,comp=o(XB u^(45/16)). If one only transports same-anchor groups, the sharper factor u^alpha holds. Both statements can be applied to the rough positive-drift occupation with smaller weights; neither bounds natural matched-ascent ledger after arbitrary deletions.

Mixed comparable/small-q same-slot products and small-q/small-q products remain. By Cauchy they are bounded by the geometric mean of the two aggregate slot energies, so if both diagonal block energies are o(XB u^3) then mixed is too; this does not supply the small-q bound. Distinct-slot CROSS remains under the previous adaptive thin/imbalance reductions. The gain energy upstream may be large because incoming waits can be short and n_A can be much larger than W_A. There is no direct inequality of the form q n_A^2<=constant times previous natural clock energy for arbitrary events. A future transfer must retain the actual selected-gain and deficit ledgers or use source-weighted tails. Equations (2),(4) are genuine o(XB) linear masks; (5) is conditional.

## 5. Reproducible finite diagnostics

First standalone audit research/min_clock_rough_anchor_transport_audit.mjs, commit df22cea9872ffb88eb74f9f136ab299aac40ec3f, exact readback blob 814f246dfa9b3dee6cf52cabcaa53e4e6e7365d7. Second independent slot audit research/min_clock_rough_slot_gain_audit.mjs, commit ee7a062fc86e1a8b29e6a0a7685d3ccd7bae40d6, exact readback blob d65a76fdb1140adff3e1167fabb4cd23915821b5.

Run from repo root:
    node research/min_clock_rough_anchor_transport_audit.mjs 1024 4096 16384 65536
    node research/min_clock_rough_slot_gain_audit.mjs 4096 16384 65536
Actual audit functions executed in available JS runtime, not a separate Node run. First: 4 X times 2 parameter modes times 2 occupations=16 combinations; second: 3 X times 2 modes times 2 occupations=12. Literal parity-gcd MIN stepping, original individual cutoff, complete crossing waits, deterministic low-suffix oracle 128 instances per first run; verifies low barrier, unique rough target and clock slot, exact incoming phase including odd q=3 exception, actual ancestor counts and relaxed weighted candidate envelope, root-only distance cap, exact linear and quadratic ledgers, and conditional gain transport. Second independently replays all roots and checks local arithmetic slot envelope and transport for whole comparable slot weights after thin deletion. Floating-point weighted energies use tolerance. Stress D=floor(B/4), L=30,y=5, comparable q>=r/2, cap=12. Analytic finite L=2 and rough cutoff often small, so the eventual sieve saving is NOT numerical extrapolation. The audit uses natural chosen occupations before common-cell instability or other earlier masks, not a cumulative branch residual.

Largest X65536,B678, stress D169,rough r>=43, max LOW gain14, at most3 actual root-only tags per occupied horizon, 5597 actual labeled rough targets, 645 comparable, actual sum of their r weights66525 versus relaxed candidate envelope75924609 (872485 keys). The relaxed envelope is very loose at this scale. Root-only total visit incidences5231 across full prefixes. Table:
| Occupation | Natural rough R | root-only R deleted | thin comparable R deleted | retained E |
|---|---:|---:|---:|---:|
| late HIGH |303919|0|1651|14753744.44|
| full positive |3601919.5|218259|66456|202690589.09|

Largest stress retained same-anchor comparable E4622665.16 late,40781303.48 full positive; same-anchor small-q E9951586.94 late,105741864.71 full positive; all distinct-anchor cross E179492.34 late,56167420.90 full positive. Same-slot comparable total E4642516.65 late (19851.49 distinct-anchor cross),41500505.97 full positive (719202.49 distinct-anchor cross). Max actual comparable anchors per occupied slot2, relaxed maximum35/44. 1/4 nontrivial multi-anchor slots. Actual upstream G83010631 late,107846173 full positive, far above the transported E; the conditional bound is loose and is NOT an empirical contraction. Finite deleted linear fractions do not establish the limiting little-o.

Largest analytic full-positive rough R5085408.5, root-only deletion82272, thin comparable448397; retained E257751778.25. The adaptive rule from section3 is not numerically measured separately. These are diagnostics of the stated local reductions, not a full energy or twin certificate.

## 6. Next target

For small-q anchors leading to a long rough wait, (1) localizes their latest nonLOW event but its small selected gain may be amplified by r(C)/q. In stationary OLD the shared pair spans D ticks inside the rough wait; its true deficit rise from the anchor is at least 2D-L. Investigate a compatible first-rise/selected-gain ledger that charges that amplification, or a weighted ancestor-mass estimate at the latest small-q anchor. For comparable thick anchors, bound G_rough,comp by source-tagged incoming gain and actual deficit crossings rather than by the relaxed key count. Retain distinct-slot residual and natural MED destination accounting from prior checkpoints. Main and all other branches unchanged; no Lean compilation.
