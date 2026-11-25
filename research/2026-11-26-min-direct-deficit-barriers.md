# Downward deficit barriers and scale-specific recovery supply

Continuation of [4947f42](https://github.com/tara-sooo/A166944-Lean/commit/4947f42966716b1daa57b1d438073e2ae52fc523). Earlier barriers constrained horizon H. Here the ordinary deficit itself has deterministic modular barriers for downward crossings. This excludes small recovery labels from the injective level-matching theorem, yields a weighted budget for genuine ordinary decreases in a restricted label band, and supplies an upper bound on the very-large-A1 tail count. For one fixed deficit level we also give a congruence upper bound for repeated small-label high-multiplier recovery. No contradiction with finite twins or Lean kernel verification.

## 1. Exact downward-cut geometry

In the established adaptive MIN model, an event with label s, side e=1-2I (I=0 even,1 odd), wait w>=1, gain g=s-1 has pre/post ordinary deficits d,d' with
    d'=d+2w-(s-1).
Both deficits are even and nonnegative along canonical rays. For s>=5 the adjusted D=d'-6I is a nonnegative multiple 2hs of s, with h>=0, where h=0 is reset. A decreasing event has d-d'<=s-3. Label3 never decreases d (gain2,w>=1).

For any positive even deficit cut b, a downward crossing means d'<b<=d. If s>=5 crosses it, then necessarily
    b mod 2s in {2,4,...,s-3} union {8,10,...,s+3}.           (1)
Indeed b-d'=b-2hs-6I is a positive even integer <=s-3. Thus define a set of allowed barrier residues modulo 2s as the complement of that union among the s even residues. For s=3 all three even residues are barriers. For s=5,7 the allowed sets are respectively {0,4,6}, {0,6,12}. For s>=11 the two forbidden intervals overlap or abut; their union is every even residue from2 to s+3. The allowed set is {0,s+5,s+7,...,2s-2}, of cardinality (s-3)/2.

Every even b congruent to an allowed residue is impossible to cross downward by label s, independent of h, time, phase, or factorization of H+-1. This is a NECESSARY geometric test for crossing, not a sufficient event-realizability criterion. It also excludes resets of label s, since h=0 satisfies the same formula. In particular all multiples of
    K_S=2P_S, P_S=product of odd primes<=S,
are downward deficit barriers for every label<=S. The previous horizon barrier works in the opposite coordinate; here a nonunit event may cross a horizon cut while not crossing a deficit cut, or vice versa. They are not being identified.

A useful second explicit barrier is b=P_S+5 for S>=5. For each odd prime s<=S, P_S is an odd multiple of s, so b=s+5 mod2s. This is 0 for s5,12 for s7, and an allowed residue for s>=11. Label3 poses no restriction. Thus this half-primorial-plus-five cut also cannot be crossed downward by any label<=S.

## 2. Dense deficit barrier family

Let D_S be the positive even integers whose residues are allowed for ALL odd primes<=S in (1). Set
    a_3=3,a_5=a_7=3,a_s=(s-3)/2 for s>=11,
    A_S=product_{odd primes s<=S} a_s,
    theta_S=A_S/P_S.
The notation theta_S denotes deficit-barrier density (not the earlier horizon barrier alpha_S). CRT on b/2 gives exactly A_S allowed cuts in every period of P_S even positions, absolute width K_S. For even endpoints u<=v with u>=0,
    |#(D_S intersect (u,v]) - theta_S*(v-u)/2| <= A_S.       (2)
For real endpoints the RHS may be enlarged to A_S+theta_S. In particular the normalized count 2/theta_S times the number of cuts has interval discrepancy <=K_S (or K_S+2 for real endpoints). Each event with label<=S crosses zero such cuts downward. Each other decreasing event crosses at most (d-d')/2 cuts, and the normalized count is at most d-d'+K_S. The density satisfies theta_S>=exp(-O(S/log S)) from a_s/s>=1/4 and the elementary Chebyshev prime-counting bound. These are different allowed residues and densities from the horizon family, even though the period is the same.

## 3. Fixed-level multiplier and repeated occurrence upper bound

For a fixed positive even cut b and a decreasing nonreset label s>=5 on side I, any crossing has h uniquely specified:
    h=floor((b-6I-1)/(2s)), r=b-6I-2sh,
    h>=1, r in {2,4,...,s-3}.                               (3)
Also 2w<=s-1-r. Hence no other h can give a downward crossing of this particular level on the specified side.

The usual selected cofactor q=(H-e)/s is odd. Writing U=n-2I at the winning tick, U=s*((q+1)/2+h), and U has parity I. Consequently
    H = e+s*q = e+s*(2I-2h-1) mod 4s.                     (4)
At this fixed level, fixed s and I, every downward crossing therefore has pre-horizon in ONE residue class mod4s. Distinct such events on an actual ray are separated in horizon by at least4s, even if arbitrary other events occur between them. This is a specialization of the earlier equal-adjusted-deficit lattice to a prescribed level; the level makes h unique. For a contiguous block of total horizon gain G, at most floor(G/(4s))+1 events of that fixed side/label can cross b.

In particular, for labels S<s<=V and no resets, the total supply of downward crossings at b is at most
    sum_{S<s<=V, s prime} nu_b(s)*(floor(G/(4s))+1),        (5)
where nu_b(s) is the number of I in {0,1} satisfying (3), hence 0,1,2. For b in D_S every s<=S is excluded. More generally (5) applies to all s>=5 when S is below5. Each marked A1 label p with p/5<b+3<=2p crosses b upward. Upward-to-next-downward pairing at b shows that the number of those marks cannot exceed (5), plus N+2 and the number of nonreset downcrossings with label>V, where N counts canonical visits in the block (at most N+1 decreasing resets and one pending upward crossing). This is a rigorous multiplicity bound even when h is large. Summing (5) at unrestricted cutoffs is still too weak for a contradiction: it permits order G/s occurrences of a fixed label and has no automatic further h-dependent sparsity.

## 4. Injective geometric matching at deficit barriers

Write x=d+3, and recall marked A1 p>=47,p>=5d+15,D=2p gives x_pre<=p/5,x_post>2p. A decreasing nonreset satisfies x/x'<3/2 and x'>=2s+3. Fix a mark lower bound T>=47 (all marked p>T), and any cutoff S>=5 with K=K_S<=T/200. We may choose T larger than S and not necessarily equal to the earlier R. Put
    beta=3/2+10K/T.
For any phase a in [1,beta), use geometric reference levels
    z_j=(T/5)*a*beta^j, j>=0.
Round UP to the next admissible multiple-cut level
    y_j=3+K*ceil((z_j-3)/K).
Thus z_j<=y_j<z_j+K, and y_j-3 is a downward deficit barrier for every label<=S. Keep reference levels through2C, where C bounds marked labels. The successive rounded levels have ratio>=3/2:
    y_(j+1)>=beta*z_j >=(3/2)*(z_j+K) >(3/2)*y_j,
since (beta-3/2)*z_j>=2K. Therefore a decreasing nonreset crosses at most ONE rounded level. The total number L of reference levels is <=1+log_beta(10C/T).

For mark p choose all reference levels in
    p/5 < z_j <= 2p-K.
The rounded levels lie in (p/5,2p] and are crossed upward by the mark. There are five or six: the multiplicative ratio is 10-5K/p>=9.975, while beta<=1.55 has beta^5<9.975 and beta^6>10. Pair each marked upward crossing to the first later downward crossing of that rounded level. As in 4947f42, assignments to nonreset events are globally injective; at most (N+2)L slots are lost to decreasing resets and the end of a finite block. But now EVERY assigned recovery label satisfies s>S, not just s>=5. For rank k (low to high) we have
    S < s < y_j/2 <= beta^k*p/10+K/2,
    s<p,
    hs>beta^(k-1)*p/15-9/2.                              (6)
The last follows from x'>2y_j/3 and x'=2hs+6I+3. For any U>T and k<=5 this implies at least k times the number of marked p<=U, minus (N+2)L, distinct decreasing nonreset events with
    S<s<beta^k*U/10+K/2
(where a non-strict upper bound on the expression also suffices). The number of complete marks is at least m-(N+2)L. These are actual decreases, not changes of the earlier cut-adjusted horizon potential.

Average the phase log_beta(a) uniformly over [0,1). The expected slots per p is log_beta(10-5K/p), so some phase has at least m log_beta(10-5K/T) total slots. With K/T=o(1) this is (log(10)/log(3/2)-o(1))*m; the proportion of six-slot marks is at least log_beta(10-5K/T)-5. This is a choice of deterministic grid, not a probability model of trajectories.

## 5. Weighted actual-reduction budget using all dense deficit cuts

Fix any collection of m marked A1 with T<p<=U (T>=47, U>=T), cutoff S>=5, optional recovery cap V>=S. For every mark p, match ALL dense deficit cuts b in the real interval (p/5-3,2p-3] to their first subsequent downward crossing (x=d+3). There are at least theta_S/2*(9p/5-K_S-2) slots per mark by (2); the interval is positive for T>=47. At any fixed cut there is at most one pending marked crossing, and a downward event can pay at most one slot per cut. The assignments may not be injective across different cuts, but their count is bounded by the actual event's downward interval capacity.

Every nonreset assigned to mark p has S<s<p<=U, since d'<b<=2p-3 gives 2s+3<=x'<2p. Also x>=b+3>p/5, x/x'<3/2 gives hs>p/15-9/2. Let H_{V,U} be the number of ordinary-decreasing nonresets with V<s<U in the block (zero if V>=U). Discard reset assignments, these above-cap assignments, and pending slots. All selected levels satisfy 0<b<=2U; each reset or above-cap event spoils at most theta_S/2*(2U+K_S+2) slots, and the same bound holds for the endpoint. Define
    B = (9/5)*sum_mark p - (K_S+2)*m
                         -(2U+K_S+2)*(N+2+H_{V,U}).
Then the number J_slots of surviving matches satisfies 2 J_slots/theta_S>=B. All surviving events decrease actual ordinary d, with S<s<=V and s<U. Let F be the total actual decrease of ALL such events in the block, and j their count. By the individual cut capacities from section2,
    F >= theta_S*B,
    F+K_S*j >= B.                                      (7)
Negative B merely makes these lower bounds vacuous. No reset or high-label exceptional mark weight is silently discarded. We paid only their actual possible cut capacity. The same proof for any marked subset p>=W restricts the counted recovery events further to hs>W/15-9/2. This yields simultaneous label-scale and high-multiplier constraints.

Compared with the continuous slab theorem, (7) sacrifices a density factor or a count correction but excludes low labels<=S. It does not claim that every downward event of label>S crosses a D_S cut, nor that the stronger uncorrected coefficient9/5 for a restricted band is proved.

## 6. Upper bound on the very-large-A1 tail

A separate choice of deficit levels applies even when K_S is too large for the rounded fine-grid construction. For S>=7 let P=P_S>=105 and take the levels in x-coordinate
    y_0=P+8,
    y_j=2^j P+3, j>=1,
retaining only y_j<=2C. The associated deficit cuts are P+5 and multiples of K_S, hence barriers for labels<=S. Each ratio of successive levels is >=3/2 and <2 (P>=18 suffices for the first). If p is any marked A1 with
    2p>=P+8,
there is at least one such level in (p/5,2p]. Indeed if p/5<y_0 use y_0; otherwise the first level >p/5 is at most twice p/5, hence <=2p. Choose just ONE per such mark and perform the same next-downcrossing matching. A nonreset can pay at most one selected slot and has s>S. If H_S counts all ordinary-decreasing nonresets of label>S in the block, the tail count M_tail of marked A1 p>=(P+8)/2 satisfies
    M_tail <= H_S+(N+2)*L_tail,                     (8)
    L_tail<=1+log_2(2C/P)+O(1).
If the first level is above2C the tail is empty. This is an upper bound on actual A1 occurrences, not just distinct labels. For the diagnostic S5 one can skip the first doubled level to preserve separation, with ratio<3 still enough to guarantee a level in the mark interval.

## 7. Consequences in macroscopic windows

Take the established crossed [X,lambda X] blocks on an infinite canonical ray, fixed lambda>1, R=floor(c log X), 0<c<1/(8log2), P=P_R<=X^delta, delta=4c log2<1/2, and S=floor(a log R), 0<a<1/(4log2). All sufficiently large windows have S>=47 and K_S=o(R). Suppose N=o(sqrt X) and the count of high-far B with p>R is o(sqrt X). Let m be ALL A1 p>R. Earlier gain-share and barrier bounds give
    m>=((lambda-1)/14-o(1))*X/P,
and m dominates sqrt X times any fixed power of log X. Every decreasing nonreset p>R is B (A1 increases, A0 resets, the deterministic test exhausts the low-deficit alternatives). There are O(sqrt X) near events, so H_R=O(sqrt X).

First apply section4 with T=R, K_S=o(R) and the maximizing phase. Reset/endpoint exceptions (N+2)L=o(m), and the number of assigned events with s>R is <=H_R=o(m) by injection. Thus all but o(m) marks have at least five distinct subsequent ordinary-decreasing nonreset recoveries with
    S<s<=R.
At least (log(10)/log(3/2)-5-o(1))*m have six such distinct recoveries. The per-rank s/p upper bounds of 4947f42 hold with an additive o(p). All these recoveries are genuinely B for sufficiently large X (s>S>=47). They are far since s<=R=O(log X) while their pre-horizon is of order X. This removes the uncontrolled p<=S population from the previous ordinary level-matching theorem, without demanding that the recovering events cross a horizon cut or bounding their h.

Second use section6 with cutoff S replaced by R. It follows that
    #marked A1 with p>=(P_R+8)/2 <= H_R+O((N+2)log X)=o(m).  (9)
So almost every marked A1 has label <P_R/2+4, not just O(P_R). This is a count restriction; it gives no claim that the exceptional tail has small total gain.

Third, choose c even smaller so delta<1/4, and apply (7) to the marks p<U=(P_R+8)/2, with T=R and V=R, using the original lower cutoff S~log R. These marks number m_*=m-o(m) by (9). Their weight W_* satisfies W_*>=R m_*. Since K_S=o(R),
    (K_S+2)m_*=o(W_*).
Moreover U=O(P_R), N+H_{R,U}+2=O(sqrt X), hence their product is O(P_R sqrt X)=o(Rm) from P_R^2=o(sqrt X). Thus (7) gives for the genuine ordinary reductions F of far nonreset B in the band S<s<=R (and their count j)
    F >= (9/5-o(1))*theta_S*W_*,
    F+K_S*j >= (9/5-o(1))*W_*.                      (10)
In particular F=Omega(theta_S R X/P_R), with theta_S>=R^(-o(1)). This is a weighted lower bound for actual ordinary decreases in the growing lower label band, without assuming j=O(m). If j=O(W_*/R), K_S*j=o(W_*) and the second inequality gives F>=(9/5-o(1))*W_*. The conditional version (7) additionally localizes large-multiplier recoveries for any moderate marked tail p>=W, but its error must be compared to that tail's weight; it need not be negligible for a small tail.

Equations (5),(8) are upper bounds, and (9) rules out a particular high-label population. They are not enough to cap all lower-band B recovery: (5) still allows many repeated occurrences, and neither sparsity hypothesis is forced by finite twins. No twin-prime contradiction. In particular this work must not be interpreted as an argument that a fixed integer trajectory stops.

## 8. Diagnostics and persistence

[Audit 46bc159](https://github.com/tara-sooo/A166944-Lean/blob/46bc159a4084e92c0e88f6cdcdc5838892106b1c/research/min_direct_deficit_barriers_audit.mjs), blob 5e603c89f1325abed8c4761cef4155610e00708f. Exact remote readback. Run node research/min_direct_deficit_barriers_audit.mjs 60000 180. Actual ECMAScript execution in tool runtime, not a separate Node process.

29,998 canonical odd roots M5..60000,549,085 events,5,254 A1, all terminated within180. 97,045 decreasing events (62,821 nonreset,34,224 reset). Complete deficit-cut periods S5/7/11/13 gave (P,A)=(15,9),(105,27),(1155,108),(15015,540). 388,180 downward-cut capacity/noncrossing checks incl resets,434,215 per-level unique h tests,62,821 fixed-h horizon-class checks,1,116 repeated same-level/same-label/same-side spacing tests,93,810 half-primorial/level geometry checks. 43,461 marked block/cutoff tests (R47/71/101,S5/7/11 plus witness),43,767 marked incidences,75,241 dense nonreset matching pairs,210,801 allocation capacity tests,37,710 matched low slots; 43,461 tail bounds,28,576 tail marks,80 tail nonreset matches. Counts overlap across blocks/cutoffs and do not represent independent trajectories. All final assertions passed. The weighted audit directly checks per-event slot capacity and ordinary total; equations (7),(10) follow from the symbolic discrepancy and exception estimates above, not empirical asymptotics.

Reconstructed the earlier exact 9,962-digit canonical witness with event word7687/5233/3541/2389/1621/1093/733/7369;22,195 literal BigInt GCD ticks,20,600 stage-residue checks. At R7500,S5, three phases1,5/4,7/5 each give five rounded multiple-cut matches, no reset/end/above-cap loss. Every phase has 4,151 matched dense low slots, hence normalized count 2*4151/(9/15)=13836.666... within actual ordinary decrease13908. The small scanned roots do not satisfy K_S/T<=1/200 at these diagnostic R, so rounded matching tests use the constructed witness, not the normal finite scan. An initial attempted witness reconstruction failed a literal assertion; the final source uses the earlier verified CRT reconstruction verbatim. The initial half-primorial grid had insufficient separation at diagnostic S5 (P15); the final source skips the first doubled level at that cutoff, and all checks were rerun successfully. Analytic rounded matching uses exact rational inequalities; the audit's discrete density lower check uses small-scale floating comparison, not an analytic proof. Main and siblings unchanged. No Lean kernel verification, external novelty claim, macroscopic infinite-ray observation, or twin proof.

Next: investigate whether the fixed-level supply bound (5) can be strengthened by simultaneous constraints at several deficit levels or by competing smaller clocks; alternatively exploit the distribution of dense deficit barrier gaps to sharpen the tail threshold in (9). The current gain and count bounds are necessary conditions only.
