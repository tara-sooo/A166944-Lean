# Bounded-multiplier close transitions: a double sieve and relay–variation tradeoff

Continuation of [9101eac](https://github.com/tara-sooo/A166944-Lean/blob/9101eacff72aa1403eb65f79182818798462783c/research/2026-11-26-min-direct-return-variation-cover-and-moving-strata.md). The previous variation estimate was for returns of the same label, and its capacity theorem required local bounded support. Here use transitions between DISTINCT selected labels instead, when the adjusted multipliers are bounded and intervening gain and ordinary post-deficit difference are small. A dimension-two sieve in the label parameter, followed by a second dimension-two sieve in the horizon progression, yields a summable dyadic estimate. The resulting relay–variation tradeoff requires no bound on the number of distinct labels and no assumption of finite twins. It does require bounded positive multipliers for the selected population. No Lean kernel verification or twin-prime contradiction.

## 1. Two-event arithmetic and an automatic long successor

Use actual adaptive MIN on a physical contiguous event block with pre-horizons in [X,Y], Y=lambda X for fixed lambda>1, total gain G=O_lambda(X), cap C=floor sqrt(Y+1). At an event let p be the selected odd prime, g=p-1, wait w, side I in {0,1}, e=1-2I, H=e mod p, ordinary deficit d=2t-H, ordinary post-deficit d'=d+2w-g, adjusted D=d'-6I. A nonreset p>=5 has D=2hp with positive integer h. Fix a positive integer multiplier cap M independent of X. Fix T>=X^a for some fixed a>1/14 and T<=C; the application uses any preceding T_k, in particular the cube threshold T_3, so this power condition holds. Take X sufficiently large that T>M, T>=11.

Select ANY subset of the physical nonreset events with p>=T and 1<=h<=M. No clock length, primality of cofactors, crossing, or support restriction is imposed on these selected events. Order them by physical time. For two successive selected events, write p,h,I,e,H,d'_1 for the first and r,k,J,f,H_2,d'_2 for the second. Let E=H_2-H-(p-1)>=0 be the total gain of all intervening (unselected) physical events. It is even. Set
    v=d'_2-d'_1,  c=v/2-3(J-I).
The exact identities are
    H_2=H+p-1+E,
    k r-h p=c.                                           (1)
Let B,A be nonnegative integers with
    B<T-1, A/2+3<=T/2.                                    (2)
Call the transition close when E<=B and |v|<=A.

A close transition cannot have r=p. For two occurrences of p>=5, their distinct odd cofactors have difference at least2, so H_2-H>=2p-2, giving E>=p-1. This uses no prime-cofactor hypothesis. Also c!=0: if c=0 and p!=r, p divides k and r divides h, contradicting k,h<=M<T. For each close pair |c|<=A/2+3<=p/2, so r is comparable to p:
    p/(2M)<=r<=2M p.                                     (3)
Both constants are fixed for fixed M. More generally, without a multiplier cap, gcd(h,k) divides c, and c=0 with distinct labels implies adjusted D>=2pr. If h=k and p!=r, then |v|>=4h-6. These exact restrictions indicate what must be handled if the multipliers are allowed to grow; they do not bound the number of such transitions by themselves.

There is an additional clock consequence. For every physical event |d'-d|<=5g by w<=2p, including p=3. The net ordinary deficit drift u=d_pre,2-d'_1 of the intervening steps thus has |u|<=5E. The second clock satisfies
    2w_2=(r-1)+v-u.
In particular when
    A+5B <= (T-1)/2,                                      (4)
every close transition has 4w_2>=r-1. More precisely |2w_2-(r-1)|<=A+5B. Therefore the SECOND event is automatically long, even if the first is fast and even if we did not filter the list by wait. Its neighboring integers have every prime factor >=w_2/2>=(r-1)/8, by the earlier competing-clock lemma. At T=T_3 the second cofactor is prime by the previous cube certificate. We use this automatic long successor in the sieve below. Alternatively if the first event is assumed long, (4) may be dropped and its pre-horizon used for the same sieve. Condition (4) holds automatically for the polylogarithmic cutoffs in the asymptotic tradeoff.

## 2. Sieve in the prime-label parameter

Fix h,k in [1,M], sides I,J, a nonzero integer c with |c|<=A/2+3, and E<=B. Write g0=gcd(h,k). Equation (1) has no integer solutions unless g0|c. Otherwise put a0=h/g0, b0=k/g0, c0=c/g0. Choose one integer solution p0,r0 to b0*r0-a0*p0=c0. All integer solutions are
    p=p0+b0*z, r=r0+a0*z.
For p in a dyadic band U<=p<2U, z ranges over an interval of at most O_M(U+1) integers. Both p,r are primes >=T. For odd sieve primes l not dividing a0*b0, the two forbidden z residues are distinct except when l|c0, as follows by taking the determinant of the two linear forms. Omit the bounded exceptional primes l<=M and use the earlier dimension-two upper sieve with the collision factor
    J(c)=prod_{odd prime l|c} l/(l-2).
This gives, uniformly in nonzero c and all translated parameter intervals,
    #admissible (p,r) in the band <<_M U J(|c|)/log^2(2U).  (5)
To justify the fixed-prime omission: in the earlier Selberg denominator for all generic two-residue primes, omit primes dividing the fixed slopes or <=M and primes dividing c0. Splitting the divisor sum according to the omitted factors loses at most the product of their local factors l/(l-2), bounded by a constant depending on M times J(c). The same weights, CRT error z_sieve^6, and harmonic lower bound give (5) with cutoff a small power of U, e.g. floor U^(1/12) for large U. By (3) it is below both prime labels. If a small prime has one root rather than two, omitting it is a valid upper bound. This also follows from the fixed-dimension sieve proof in the previous cluster note.

The exceptional factor has bounded mean, uniformly in the cutoff:
    sum_{1<=m<=A/2+3} J(m) <= e*(floor(A/2)+3).
This is the earlier elementary singular-factor average, obtained by expanding J(m) over odd squarefree divisors and using the convergent product with factors 1+2/[l(l-2)]. Consequently summation over c costs O(A+1), not an additional worst-case loglog factor. Constants can depend on M but not on A,B,X.

## 3. Independent horizon sieve in the actual CRT progression

For a fixed admissible pair of distinct labels p,r and fixed e,f,E, the necessary horizon congruences are
    H=e mod p,
    H+p-1+E=f mod r.
They determine one residue H_0 modulo pr. The evenness of H may be ignored for an upper bound. All candidate H in [X,Y] lie in a progression
    H=H_0+pr*u
with u in an interval of at most O_lambda(1+X/(pr)) integers.

By (4), the actual successor horizon H_2=H+p-1+E has both neighbors rough to (r-1)/8. For a small odd prime l different from p,r, the two conditions l|H_2-1 and l|H_2+1 exclude TWO distinct residues of u, since pr is invertible mod l. Apply the dimension-two sieve to this u interval with cutoff floor N^(1/12), N its length (small lengths bounded trivially). It lies below T and below the certified roughness cutoff for large X: N=O_lambda(1+X/T^2) and a>1/14 ensures (1-2a)/12<a when a<1/2. This shows
    #admissible H <<_{lambda,M}
       (1+X/U^2)/log^2(2+X/U^2),                        (6)
using (3). In the alternative first-long version apply the same argument to H+-1. The sieve conditions in (5) and (6) are not probabilistic independence: (6) is uniform for EVERY pair counted in (5) and every fixed shift. We multiply two deterministic counting bounds.

For each tuple p,r,h,k,c,I,J,E,H there is at most one occurrence as a close transition between consecutive selected events on the fixed monotone ray: its first pre-horizon H identifies a unique actual event and its selected successor is unique. In fact the sieve counts necessary arithmetic candidates even without knowing the ray. Charge each close pair the gain r-1 of its ending event. By (3) this is O_M(U). Multiplying (5),(6) by this gain shows for the dyadic band and fixed h,k,c,I,J,E that the total charged gain is at most
    O_{lambda,M}( X J(|c|) /
             [log^2(2U)*log^2(2+X/U^2)] ).                (7)
Here U<=C=O_lambda(sqrt X), so 1+X/U^2 is comparable to X/U^2. The band lower endpoint can be taken >=T/2, hence log(2U)>>_a log X.

The second sieve is essential for summing over scales without losing one logarithm. Choose bands with U comparable to C*2^(-j), j>=0. Then log(2+X/U^2)>>_lambda (j+1), uniformly. Thus the sum over all bands U>=T/2 of 1/log^2(2+X/U^2) is bounded by a constant times the convergent sum (j+1)^(-2). Summing (7), over the bounded h,k and sides, over at most B+1 E values, and using the mean of J in section 2 for the O(A+1) nonzero c, proves the new close-transition supply theorem:
    F_close <<_{lambda,M,a}
           X (B+1)(A+1)/log^2 X.                         (8)
Here F_close is the total ENDING-event gain of close consecutive selected transitions. It applies to all selected nonresets satisfying the bounded multiplier condition, not just certified long events, when (4) holds. It also holds with (4) replaced by first-long selection, as described above. No assumption of finite twins, no bounded-support cover, and no small variation assumption is used in (8). The bound need not be nontrivial for large A,B. In particular (B+1)(A+1)=o(log^2 X) forces F_close=o(X), uniformly over the chosen subset and the actual ray. The two sieves are necessary-condition counts, not a proof that any candidate transition is realizable.

## 4. Relay–variation inequality and a product obstruction

Let F be total gain of the entire chosen high bounded-multiplier nonreset population, U_out=G-F total gain of all physical events outside it, V_d=sum of |d'-d| over the block. The intervening intervals defining E for successive chosen events are disjoint, and sum E<=U_out. The post-to-post intervals for v are disjoint as well, so sum |v|<=V_d. The first chosen event costs at most C. Every other chosen event ends a consecutive selected transition, either close, or with E>B, or with |v|>A. The number of the latter two types is at most U_out/(B+1) and V_d/(A+1) respectively (all quantities integer). Each ending gain <=C. We conclude
    F <= C + O_{lambda,M,a}(X (B+1)(A+1)/log^2 X)
            + C U_out/(B+1)+C V_d/(A+1).                 (9)
For first-long selection use the corresponding alternative to (4); for arbitrary selected bounded-multiplier nonresets choose (2),(4). This inequality contains no selected-support-size parameter and does not charge any unselected relay or physical variation twice. It is valid for an arbitrary subset, not merely a maximal selection.

Suppose F>=delta X for fixed delta>0 along macroscopic crossed windows. There is a positive constant depending on delta,lambda,M,a such that
    (1+C U_out/X)(1+C V_d/X) >>_{delta,lambda,M,a} log^2 X. (10)
Proof: write x=C U_out/X and y=C V_d/X. If (1+x)(1+y)>log^2 X there is nothing to prove. Otherwise take B=ceil(K x), A=ceil(K y), with K a sufficiently large fixed constant depending on delta, e.g. K>=8/delta. Both are O_delta(log^2 X), so (2),(4) hold for sufficiently large X. Then the last two terms in (9) are <=2X/K and C=o(X). The first big-O term is at most K' X (1+x)(1+y)/log^2 X for a fixed K'. To have F>=delta X requires (1+x)(1+y)>= (delta/(2K')) log^2 X eventually. This proves (10), including x=0 or y=0, since the corresponding terms in (9) vanish. One can retain constants from (8) if desired; no numeric sieve constant is claimed.

In particular the arithmetic-geometric mean inequality gives
    U_out+V_d = Omega_{delta,lambda,M,a}(X log X/C)
              = Omega(sqrt X log X).
If U_out=O(X/C), then V_d=Omega(X log^2 X/C); if V_d=O(X/C), then U_out=Omega(X log^2 X/C). More generally, whenever both normalized budgets diverge, (10) requires their product at least a constant times log^2 X. The interpretation is a quantitative restriction on nearly consecutive, nearly flat high events with bounded multipliers, even when each event uses a NEW prime. It improves the former flat-support reasoning for this regime by not needing any partition into few-label blocks. It does not imply V_d=Omega(X), nor is it an upper bound on the full variation.

At the preceding cube crossing threshold T_3, select all actual high nonreset crossers with h<=M, optionally first-long. If the small-crossing mass M_<T is o(X), the previous theorem ensures total outside-high-crosser gain U=o(X). But U_out in (9)-(10) also includes reset gain and gain of crossers with h>M (and, if selected, fast exclusions). Thus we cannot replace U_out by U alone. Even if those additional populations are negligible on the macroscopic scale, the smoothing error does not give U_out=O(sqrt X). The new bound rules out a much more restrictive regime of jointly small relay and variation budgets. Under the cube certificate each close successor in (8) has prime cofactor, but no twin pair is necessarily produced; the theorem holds unconditionally. To exclude the full large-event alternative, one would still need control on the unbounded multipliers, on the relay/variation budgets at the scales in (10), or a direct twin witness. The elementary identity (1) also gives a separate necessary large-multiplier mechanism for close c=0 transitions with distinct labels, D>=2pr, and for h=k transitions, |v|>=4h-6. These are possible starting points without a fixed multiplier cap.

## 5. Diagnostics and persistence

[Final audit 88b50a3](https://github.com/tara-sooo/A166944-Lean/blob/88b50a3a8fcfc79d46f59febafb6d845c820bf64/research/min_direct_close_transition_double_sieve_audit.mjs), blob 528877e960d0728709223ba4d43c597333759bb5, exact remote readback. Run node research/min_direct_close_transition_double_sieve_audit.mjs 40000. Executed the actual ECMAScript function in tool runtime, not a separate Node process. 19998 odd canonical roots through40000,352451 actual events,0 unresolved cap180. 116934 nonempty block/cutoff controls,185650 selected incidences,121029 consecutive filtered pairs and exact linear/gcd-divisibility checks,3505 same-label relay checks,34681 equal-multiplier distinct-label lower checks. 4063 close incidences (1998 direct,2065 with positive relay;307 zero ordinary change,2430 different multipliers),88785 large-relay and28181 large-variation incidences. 4063 exact CRT/relay-drift/tuple-capacity controls,18617 each roughness and progression forbidden-residue checks. All 116934 exact gain-budget tests passed. For the second mode without a first-long restriction,58467 nonempty controls,691 close pairs all verified to have automatically long successors,114 with a fast first event. No cube-certified second event in this small finite scan; the cube implication follows from the previous factor certificate and (4), not from a positive cube example in this audit.

Independent finite controls:1826 linear Diophantine parameter/residue systems,567886 exact prime-line residue checks,256 abstract horizon CRT systems,32512 horizon-residue checks. The earlier exact Selberg sieve audits validate the weight algebra; these new tests verify the actual inputs and progression structure of the two sieves, not a numerical verification of the asymptotic uniform constant in (8). Example actual p23,r17,h2,k3,H942,H_2=970, E6 from relay labels3,5, v4,c5 (3*17-2*23=5), waits9,4. This is in the first-long finite mode; the stronger condition (4) is not imposed on that example. All counts are overlapping incidences, not distinct transitions across all roots. All final assertions passed. No Lean executable/kernel verification, new external novelty claim or finite-twins contradiction. Main and sibling branches not modified.
