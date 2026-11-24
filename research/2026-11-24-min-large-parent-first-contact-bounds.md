# Far first-contact pairs: large-parent product bounds, near-label deletion, and stopped-cohort witnesses

2026-11-24 JST. Continues dd419d2fad044ffcb9a934dbb1c1ce3400ac1de0 on the SAME research/min-cycle-forest-2026-11-24 branch. Paper-level deductions from canonical MIN and the established upper-bound sieve, two exact finite audits. No Lean compilation. These estimates cover growing large-parent mass ranges and one full-cap arithmetic class; they do NOT establish the total far-contact bound or twin-prime infinitude.

## 1. Fixed target and exact predecessor classes

Retain dyadic X divisible by four, N=X/2 original odd M in [X,2X), B=ceil(sqrt(7X)), C0=2M-2, t0=M+2, original K(M)=floor((7M-1)/4). Use LOW7 with L=210 and uniform first-heavy selected-key absorption, initially T=ceil(B log^2 B), d=floor(T/2). Each executed high key (q,D), q>7, has whole original-tag mass m(q,D)<T; each proposed key (p,C) with mass >=T stops all its tags before execution. P_d counts ORDERED distinct original source pairs with |M-M'|>d sharing any proposed high key, once at the first such contact. J_d counts all far ordered cross-predecessor pair incidences, including later cross-class recontacts; P_d<=J_d. The predecessor class at (p,C) from (q,D) is a subset of its WHOLE earlier executed mass. A root with no previous high selection forms a singleton predecessor class. For far pairs, two initial roots at C cannot both contribute when d>L/2. The previous roadmap proves P_d >= (T-1-d) S for stopped population S, and R_pre=O(X^2/log B). Thus liminf P_d/(NT)<1/2 suffices. No-twin windows have S=N-o(X).

For two distinct non-root predecessor keys a=(q,D), b=(q',D'), with even g,g' in [0,L),
    D=C-q+1-g, D'=C-q'+1-g',
    q | C-g+eta, q' | C-g'+eta', eta,eta' in {0,2}.
At fixed q,D,q',D',g,g', the common C is determined. Each original tag has at most one proposed next high key at C (strict horizon increase), and the sets of tags using different current p are disjoint. Thus the sum of cross-products of the current subsets over ALL possible current p is <=m(a)m(b), not an extra factor of the number of possible current primes. A root class can be treated with m=1; at most O_L(1) root candidates lie within L of C. Throughout the analytic bounds we use whole predecessor masses, not current subclasses (the latter could split across p).

## 2. Unconditional product-window estimate, including large-large

Without any roughness restriction, fixed distinct q,q',g,g',eta,eta' determine one CRT residue of C modulo qq'. Counting even C gives O(1+X/(qq'))=O(X/(qq')), since qq'<=B^2=O(X). For equal q with distinct previous keys the one-prime bound O(X/q) suffices; the number of choices for g,g', signs is O_L(1). Initial-root/nonroot pairs use the same one-prime bound. Hence the total number of ordered candidate class-pair tuples (with current p omitted) is
    O_L(X (1+sum_{11<=q<=B prime} 1/q)^2)
    = O_L(X (log log B)^2).
If m(a)m(b)<=V, the total contribution to J_d (even without far separation) of this product window is <=O_L(X V (log log B)^2). In particular for V=T/(log log B)^3, it is o(NT). This covers all balanced parent masses up to sqrt(T)/(log log B)^(3/2), a polynomially growing scale in B, with neither parent required to be small or rough. For example all pairs with both masses <=sqrt B are included eventually. This is not a bound on m(a)m(b)>V.

## 3. Stronger one-power-rough count, using the actual CRT interval length

Fix 0<theta<1, call a previous key rough here if r(D)>=Z=B^theta (round upward if necessary), and suppose at least one of a,b is rough. Thus its label, say q, satisfies q>=Z. We claim the total number of candidate class-pair tuples with this property is
    A_theta=O_(L,theta)(X log log B/log^2 B).
This strengthens the earlier O(X (log log B)^2/log B) bound for the much smaller subpolynomial roughness threshold, but applies only to the power-rough range.

For distinct q,q', the admissible even C lie on a progression of step 2qq'. The available variable interval has length at most O(1+X/(qq')), and can be embedded in an integer interval of length comparable to 1+X/(qq'). For the fixed rough predecessor D=C-q+1-g, the two forms D-1,D+1 have distinct forbidden residues modulo every odd ell not dividing qq': their common slope is invertible and the difference is 2. Omit q,q' and 2; the omitted odd-prime factors increase the sieve product by at most an absolute constant. This is the same two-dimensional upper-bound sieve as in the previous projected rough-saturation note, with no conjectural lower bound. For a progression interval of length n>=2, the sieve with sufficiently small fixed power of n as level, and z a sufficiently small fixed power of n subject to z<Z, gives
    O(n/(1+min(log n, log Z))^2)
candidates. For bounded n use the trivial bound. Explicitly one may use sieve level n^(1/4) and z=min(n^c,Z^c) for sufficiently small fixed c. The uniform sieve error O(n^(1/4) log(2n)) is negligible against n/(1+log n)^2 for large n. Since log Z=theta log B and n<=O(X), the estimate is O_theta(n/(1+log n)^2) throughout. The arithmetic residue count O(2^omega(k)) and the standard upper-bound sieve are those already used in the repository, not an assumption of independence of source weights.

Split q'<=B^(theta/2) from q'>B^(theta/2). In the first case n comparable to X/(qq') is >=c B^(1-theta/2), so count O_theta(X/(qq' log^2 B)). Sum q>=B^theta (harmonic mass O_theta(1)) and q'<=B^(theta/2) (O(log log B)) to obtain the claimed bound.

In the second case define u=floor(log(B/q)), v=floor(log(B/q')), nonnegative integers <=log B. Then n comparable to 1+X/(qq') is comparable to exp(u+v), since X~B^2/7, and count
    O_theta(X/(qq'(1+u+v)^2)).
Every logarithmic prime band B exp(-(j+1))<p<=B exp(-j) restricted to p>=B^(theta/2) has reciprocal sum O_theta(1/log B), by the elementary prime counting upper bound. Therefore the sum of candidate counts is at most
    O_theta(X/log^2 B) * sum_{0<=u,v<=ceil(log B)} (1+u+v)^(-2)
      = O_theta(X log log B/log^2 B).
There are at most k+1 pairs u+v=k, so the last sum is logarithmic in log B. This step is why a single globally fixed sieve cutoff, which loses the short-interval regime, is unnecessary.

For equal q>=Z, distinct D,D' or a rough parent paired with an initial root, the progression has step 2q and length >=cB. The same two-form sieve bounds each fixed g,g',sign by O_theta(X/(q log^2 B)), summing to O_theta(X/log^2 B). Initial root choices and gains cost O_L(1). This proves A_theta.

Multiplying by a product cutoff V gives a uniform bound on the actual cross-class original-source pairs, not just candidate locations:
    J_d(rough parent, m(a)m(b)<=V)
        = O_(L,theta)(X V log log B/log^2 B).
In particular for V=T log^(2-epsilon) B with any fixed epsilon>0, the bound is o(NT). This handles two genuinely large parent groups even if each has mass as large as sqrt(T) log^(1-epsilon/2) B = O(sqrt B log^(2-epsilon/2) B), under the power-rough condition. It also covers asymmetric masses with the same product bound. It does not handle arbitrary products near T^2, or both nonrough parents at this larger scale. No source mass has been replaced by an unweighted key count.

## 4. Exact same-label exclusion and a full-cap deletion for distinct close top labels

If q=q'>L+2 and distinct previous keys share a projected successor horizon C, then D-D'=g'-g is nonzero with absolute value <L. Both D,D' are congruent to +/-1 modulo q. Thus D-D' must be +2 or -2. Since D,D' are even, if both had r>3 then both would be divisible by 3 (their odd neighbors avoid 3), which is impossible at distance 2. Consequently
    q=q'>L+2, distinct incoming keys => min(r(D),r(D'))=3.
In particular same-label mergers of two power-rough parents are impossible for sufficiently large B. This is exact at ANY source mass, including maximal allowed masses. It does not eliminate cheap/rough same-label pairs or the smaller q<=L+2 cases.

There is another unconditional deletion which allows both masses all the way up to the cap. Use the optional smaller cap T_*=ceil(B log B) (the original stop criterion and sufficient P_d/(NT_*)<1/2 hold unchanged with this cap, and R_pre=O(X^2/log^2 B)). Put Q=ceil(B/log^(1/4) B), H=ceil(log^(1/4) B). Restrict to DISTINCT q,q'>=Q and 0<|q-q'|<=H. For each fixed positive even h<=H, the standard two-form upper-bound sieve on q,q+h in a dyadic interval [Y,2Y], Y>=Q/2, counts O(Y (log log B)^2/log^2 Y) such prime pairs. To see uniformity, omit primes dividing 2h and use the two distinct forbidden residues for the others; the exceptional product is at most O((log log B)^2) since h<=H and hence log(2h)=O(log log B). Both q,q+h exceed the small-power sieve cutoff. Odd h gives no odd-prime pair. The weighted sum of 1/(qq') over such pairs is
    O(H (log log B)^2/(Q log^2 Q)).
Indeed sum the dyadic bounds divided by Y^2, dominated by the first band. Apply the CRT count at the common C and multiply by the full whole-parent cap product T_*^2. This bounds even the repeated cross-pair count, with no roughness or mass ratio requirement:
    J_close_top <= O_L(X T_*^2 H (log log B)^2/(Q log^2 Q))
                = O_L(X T_* (log log B)^2/log^(1/2) B)
                = o(NT_*).
Thus this arithmetic class of two distinct large top labels is eliminated even for both incoming masses of order T_*. In particular close predecessor horizons |D-D'|<=H-L imply |q-q'|<=H, and the same estimate covers identical predecessor horizons with distinct top q,q' (eventually H>L). For the original cap T=B log^2 B, the displayed bound is not a little-o estimate: use T_* only when applying this full-cap corollary. More generally cap B log^gamma B, top cutoff B/log^alpha B, proximity log^beta B work when gamma+alpha+beta<2. This is a partial bound on large-large, not on arbitrary distinct top labels or same-label pairs.

## 5. A bounded-degree set of stopping witnesses removes the extreme-far part at all masses

It suffices to bound pairs witnessing the stopped population, not all P_d. At every stopped group of size m>=T, partition its sorted original roots into k=floor(m/T) balanced disjoint blocks with sizes floor(m/k) or ceil(m/k), thus T<=size<=2T-1. Retain all roots. Count each ordered pair of roots in the same block at distance >d at its FIRST projected contact, including the stopped key. Call the total P_w. Blocks are disjoint across stop groups. Each block of size s contributes >=s(s-1-d) pairs; hence P_w >= (T-1-d) S just as P_d did. Each individual source belongs to at most 2T-2 other possible witness partners (bounded degree). In contrast P_d may contain irrelevant pairs from many unrelated groups.

For a separation D_far>d, the earlier source M in a witness pair with |M-M'|>D_far has accumulated horizon gain >2D_far by its stop: the common horizon is at least C0(M'), and horizons increase. By C<=2t, initial deficit 6, and each event gap<=2r(C), its executed prefix cost is >=(2D_far-6)/4. Thus the number of such earlier roots is O(R_pre/D_far), and the ordered extreme-far witness count is
    P_w(|M-M'|>D_far) <= O(T R_pre/D_far).
For T=ceil(B log^2 B) take D_far=floor(X/sqrt(log B)). This gives O(XT/sqrt(log B))=o(NT), regardless of how large either parent group is, whether any key is rough, or how often pairs meet. The analogous choice for T_* with its stronger R_pre bound can be D_far=floor(X/log B), giving O(XT_*/log B). Thus only d<|M-M'|<=D_far needs to be controlled for these witness pairs. This is a genuine removal of the extreme-far population, but D_far is still much greater than d, and the witness restriction alone does not bound the remaining pairs.

## 6. Exact audit of all projected first contacts

Code research/min_far_first_contact_audit.mjs. Run:
    node research/min_far_first_contact_audit.mjs 256 1024 4096 16384 65536 262144
Executed the function body on all six windows. Three caps floor(B/4),floor(B/2),ceil(B log^2 B) at the first five windows, latter two at X262144. Every original source and cutoff is retained. Enumerate cross-class far pairs, deduplicate original-root pair IDs over all proposed high keys; count ordered pairs by doubling unordered counts. For X<=1024 independently enumerate every far pair in every group (including same-parent pairs), and verify exact set equality. Also 16466 literal parity-GCD clock/terminal comparisons over these two windows and three caps (3423+13043). Verify exact predecessor-key partition, whole mass caps, same-label exclusion for q>L+2, P<=J, all stopped pairs present, and P>=stopFar>=(T-1-d)S. Full script and JSON committed and exact remote readback at 1b4c7c161c6e9f0deecb6e4fc3bcf5b21d3527f8.

|X|B|T=floor(B/2)|P_d|J_d|P_d/(NT)|large-large P_d|
|--:|--:|--:|--:|--:|--:|--:|
|4096|170|85|48242|54490|.277125|14660|
|16384|339|169|326890|413950|.236116|126562|
|65536|678|339|2044160|2615178|.184020|811534|
|262144|1355|677|11922336|16333126|.134358|4900998|

Diagnostic large-large means both whole nonroot parent masses >=ceil(sqrt(T)); rough means r>=ceil(sqrt B). At X262144,T677 the 4900998 large-large first contacts include 3058550 with at least one rough parent (534136 both rough), 1842448 both cheap, and 380682 with both masses >=T/4. The large-large repeated cross-class count is 8583474, so deduplication matters. There are no stopped groups at this cap; all 131072 roots have twin terminals. A concrete large contact is q=q'=31, D=868032,D'=868030, next (p,C)=(59,868068), whole parent masses 405 and 149, r=31 and 3, 93796 far ordered cross pairs of which 75382 are first. Another contact uses q=613 and 67, D=787704 and 788256, masses 432 and 136, r=5 and 5, next (743,788322): 94468 far ordered cross pairs of which 49946 are first. These show why deleting only power-rough/near-top pairs does not settle large-large. The cap ceil(B log^2 B) has P=0 in all tested windows because the separation threshold exceeds the maximum observed shared-key root distance, not because of a proved asymptotic bound.

## 7. Independent stopped-cohort witness audit

Code research/min_stop_witness_first_contact_audit.mjs. Run:
    node research/min_stop_witness_first_contact_audit.mjs 256 1024 4096 16384 65536 262144
Executed all six windows, caps floor(B/4),floor(B/2). First process every original root to determine the whole previous-key masses and final stop cohorts. Then independently replay each stopped root's exact original trajectory, reconstruct the high-key prefix buckets separately within its stop cohort, and count each pair at its first common key using its whole previous-group masses from the first pass. Verify no first pair has identical previous nonroot key, exact original stop and cutoff, exact equality of the distinct far pair count to the directly enumerated final stop-cohort pair count. Partition each sorted stop cohort into balanced blocks of size [T,2T-1] as section 5; verify degree bound and P_w >=(T-1-d) S. Also count extreme-far witnesses and confirm previous gain/cost accounting. Exact script and JSON readback at ff548151d30e250ea7377ec4ff55f881d9061ad8. The all-far stopped-cohort counts at matching caps agree with the first audit's stopFar.

At X262144,B1355,T338,N131072, 30 stop keys and 11112 stopped roots. All stop cohorts have sizes <2T so the balanced witness partition does not discard any within-cohort pairs in this case. 3279318 ordered far witness pairs, and 4270484 repeated cross-class witness incidences. Of the first witness contacts:
    1991966 large-large (60.74%);
     686264 large-large with both r<ceil(sqrt B);
     213218 large-large with both r>=ceil(sqrt B);
     763356 large-large with both whole masses >=T/4;
      53416 large-large with same previous label;
     989266 first witness contacts at the final stop itself (all mass classes).
The remaining witness pairs first meet BEFORE their final stop, so counting only incoming pairs at stop keys would miss about 70% of the target in this diagnostic. No witness pair exceeded D_far=X/sqrt(log B) in any tested window. One large stop cohort (167,904638), mass452, has 163258 far witness pairs and 118524 large-large first contacts, including 82358 with both parents cheap by the diagnostic threshold. This is a finite observation, not a uniform estimate.

## 8. What remains

We now have genuine analytic upper bounds for products of growing parent masses, a stronger one-power-rough candidate count, an exact same-label exclusion for two rough parents, a close-top class with FULL-cap masses (using T_*), and an all-mass extreme-far witness removal. The proof still lacks a bound for witness first contacts with very large parent products, especially two cheap or mixed small-label groups at intermediate source separations. The finite data exhibit these cases explicitly. Neither the unweighted CRT count nor merely taking the product cutoff to T^2 suffices. Next proof work should use the bounded-degree witnesses and the exact cutoff-tagged reverse ancestry of BOTH large parents to bound their joint source mass, rather than extending the unweighted sieve without controlling that product. The required total witness bound remains liminf P_w/(NT)<1/2 (or with T_*), and is OPEN. No new branch, no main edits, no claim of a Lean-verified theorem.
