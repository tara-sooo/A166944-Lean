# Unbounded first-return indegree by one-event stars; positive-density collision and source obstructions

Continuation of [6bdbf35](https://github.com/tara-sooo/A166944-Lean/commit/6bdbf354a5cb13f13abb6493da96acfe08e95531), same independent direct-arithmetic branch. We test the previous proposed route of bounding collision excess C(X) and crossing edges E(X). The new theorem is an obstruction to that route: collision excess has a linear lower bound, and individual first-return indegrees are unbounded, even when all incoming edges are one-event returns. This is not a finite-twin contradiction. No Lean kernel verification.

## 1. A one-event inverse formula

Canonical root L odd>=5 means (t,H)=(L+2,2L-2). F denotes first actual canonical reentry, F* allows formal quiet continuation at terminal plateaus. Fix a target odd M and p=1 mod4, p odd prime, p|M. Put k=(p-1)/2, L=M-k. Then L is odd, and its initial plateau H=2M-p-1 has H+1=2M-p divisible by p. The first odd-side p clock from L is at relative j=k: absolute n=M+2, n-2=M divisible p. Indeed for even j the relative gcd with no preceding gain is gcd(L+j,2j+1), so for 0<j<k the second argument is <p. On odd j the gcd is gcd(L+j+2,2j+7); its second argument <=p+6. If no prime <=p+6 divides H-1 and no such prime other than p divides H+1, all earlier ticks are quiet and gcd at j=k is exactly p. With M sufficiently large for p^2<=H+1, this is the actual adaptive MIN transition, producing horizon H+p-1=2M-2 at time M+2. No earlier canonical state at a new horizon is possible since there were no earlier events. Hence F*(L)=M; also F(L)=M if the target is nonterminal (and event-tick entry holds even if it is terminal under the previous event convention). We impose nonterminality explicitly below to avoid convention issues.

More generally a first return with EXACTLY ONE nonunit event has gain p-1=2(F(L)-L), so k=(p-1)/2 is positive even, p=1 mod4. If the return is on the event tick then p|M by the odd clock. If the return is on a quiet tick, the prior post deficit is 0 (deficits2,4 impossible), and the even event at n=M-1 satisfies p|M-1. Thus its root L is uniquely determined by p and M, and any such incoming label divides M(M-1). In particular the number of one-event incoming edges is <=omega(M)+omega(M-1)=O(log M/log log M), from the product of distinct primes >=(number of primes)! and the elementary factorial lower bound. This is only for the one-event subset, not a bound on the full indegree. The next theorem shows even this subset has no constant uniform bound.

## 2. Arbitrarily large stars, positive-density target sets

Theorem. For each positive integer k there is a fixed modulus and a nonempty union of odd target residue classes such that every sufficiently large M in these classes is nonterminal and has at least k distinct incoming first-return edges, each consisting of exactly one nonunit event. Thus targets with indegree>=k have positive lower density among all odd roots. The conclusion is unconditional on twin finitude.

Construction. Choose k distinct primes p_1<...<p_k, all >2k+3, all 1 mod4, all 1 mod every odd prime <=2k. Inductively require p_i=1 mod each earlier p_j and p_i>p_(i-1)+2. Such primes exist in arbitrarily large sizes: the elementary infinitude of primes 1 mod m suffices (alternatively Dirichlet). For completeness for fixed m>1, choose a sufficiently large integer A divisible by m and any finite forbidden prime set. The cyclotomic polynomial Phi_m(A)>1 and constant term1 give a prime divisor l not dividing mA or the forbidden set; x^m-1 is squarefree over F_l since l does not divide m, so its cyclotomic factors are pairwise coprime there. If l divides Phi_m(A), the multiplicative order of A mod l is exactly m (a smaller order would put A in a proper-divisor cyclotomic factor). Thus l=1 modm, giving an arbitrarily large such prime by including all smaller primes in the forbidden set. Take m to be the product of 4, the required small odd primes, and earlier chosen primes.

Set B=p_k+6. Require for each chosen p_i that M=0 mod p_i. For every odd prime l<=B impose
    2M-p_i-2 !=0 mod l for all i,
    2M-p_i   !=0 mod l for all i with p_i!=l.
These are precisely exclusions of small factors from the predecessor's H-1 and H+1 in section1.

There is a nonempty allowed set for every l:
- If l=p_j is chosen, M=0 modl is allowed. For i=j the excluded minus-neighbor residue is -2, nonzero; for i<j we have 0<p_i<p_i+2<l, so both are nonzero; for i>j we have p_i=1 modl, so -p_i and -p_i-2 are -1,-3, nonzero since l>3.
- If l is not chosen and l<=2k, all p_i=1 modl, so at most two residues of M are forbidden (2M=1 or3). Since l odd>=3, at least one remains.
- If l is not chosen and l>2k, at most 2k residues are forbidden, fewer than l.
The case k=1 with no odd primes <=2k is covered by the last case.

Finally choose an additional odd prime r>B and require 2M=1 modr. This guarantees r|2M-1 at the target and r eligible for large M, so the target is not terminal. CRT, including M odd, gives a union of residue classes modulo Q=2r*product_{odd primes l<=B}l, with positive exact density relative to odd roots
    delta_k = (1/r)*product_{odd primes l<=B} (#allowed residues of M modulo l)/l >0.
For all large M in these classes, the k roots L_i=M-(p_i-1)/2 are distinct, above the eligibility threshold, and section1 applies to all simultaneously. Their one-event edges end at exactly the same physical state (t,H)=(M+2,2M-2), not merely equal horizons at different times. They therefore coalesce forever after that time (until termination if it occurs). The construction makes no claim that all predecessor roots or targets are prime. Indeed target M is divisible by all chosen p_i, and the incoming degree may be much smaller than the trivial arithmetic upper bound in section1.

This shows that attempting to prove a uniform finite bound on first-return indegree is impossible. It does not contradict bounds growing with M, nor imply an infinite ray through these stars.

## 3. Exact collision excess from the bounded-return residue graph

Use the finite formal return graphs from the preceding note: gap<=T is periodic on sufficiently large odd M modulo 2P_T, P_T=product of odd primes<=2T+7. Let d_T(v) be the incoming degree in this finite residue graph, including only returns of gap<=T. Distinct incoming residues lift to distinct actual predecessor roots for each sufficiently large target in that residue class: their gaps are distinct (for a fixed target a gap determines its root), and the whole finite transcript lifts by periodicity. For T=2,4,6 all gaps are <2P_T, so no two such predecessors can alias as the same residue. More generally this last uniqueness is not needed for the lower bound as long as edges are counted as actual distinct predecessors.

Exhaustive exact enumeration (audit below) yields:
| T | P_T | d=0 | d=1 | d=2 | d=3 | excess C_T |
|--:|--:|--:|--:|--:|--:|--:|
|2|1155|1001|154|0|0|0|
|4|15015|12493|2392|130|0|130|
|6|4849845|3703461|988988|151126|6270|163666|

Here C_T=sum_v max(0,d_T(v)-1), and the finite exact balance S_T=C_T+(P_T-edges) is checked. The maximum incoming degree is3 at T6. The formal prefixes are sufficient for this count and use only integer GCD and least factors.

Under finite twins, for all sufficiently large roots formal and actual F agree (all are infinite). Thus the cumulative collision excess C(X) in the previous induced graph on odd roots M0..X satisfies
    liminf_{X->infinity} C(X)/(#odd roots in [M0,X])
        >=163666/4849845 = 0.0337466455... .        (1)
Only boundedly many targets near the lower cutoff lose predecessors. No issue at the upper cutoff because every predecessor lies below its target. This is an exact lower bound of about3.3747% per odd root, NOT an estimate of the full collision rate or its limit. It is much larger than the O(X/log X) scale of the prime-source count in the preceding paper.

The same qualitative linear lower bound is unconditional: impose target nonterminality by 2M=1 mod23, with 23>19. This condition is independent of the T6 period and makes the formal short incoming edges actual for sufficiently large targets. A terminal plateau cannot occur earlier in a transcript with a later event, and the target itself is active. Thus for actual F the unconditional liminf is at least (163666/4849845)/23, about0.1467% per odd root. In fact other residue classes also contribute; this is just a guaranteed subset. Section2 separately gives a qualitative linear lower bound from any fixed two-star cylinder without full graph enumeration.

## 4. A positive proportion of roots must be global sources

For the actual map (whether or not twins are finite), restrict to all odd roots5<=M<=X. It is increasing on its domain. Hence no root beyond X can point to a target <=X. The number S(X) of zero-indegree vertices in this induced graph is EXACTLY the number of global sources in that interval. Its identity S=C+E+U from the preceding paper holds with U including terminal/nonreturn cases. In particular S>=C. From section3:
    liminf S(X)/(#odd roots<=X) >=163666/(23*4849845)>0
unconditionally, and under finite twins the stronger bound (1) holds for S as well. This strengthens the previous prime-source theorem, which only supplied order X/log X. Since primes are o(X), there are a positive lower density of COMPOSITE source roots too. This is a graph-theoretic consequence of many actual merges and monotonicity, not a claim of an explicit congruence classification for the composite sources.

For each k>=2, section2 gives more generally C(X)>= (k-1)*delta_k*(#odd roots<=X)-O_k(1), with the corresponding lower bound on S. No assertion that delta_k has a useful uniform asymptotic in k.

## 5. Crossing-edge alternative from the long-wait tail

Define E(X) and U(X) as in the preceding note (fixed lower root cutoff M0), E=#defined F(M)>X, U=#undefined F for M<=X. For odd cutoffs x and root M<=x, its contribution to E(x)+U(x) equals 1 if it has no return by x (including undefined). This is the exact discrete occupancy interpretation of the gap.

Take N large, T=floor(log N/(32 log2)), and use the preceding exact density estimate: Omega(N/(log log N)^2) odd roots M in [N,2N] have W(M)>T. For every such root and every odd x with M<=x<M+T, its first return has not occurred (including terminal convention). Thus summing over odd x in [N,2N+T] yields
    sum_x (E(x)+U(x)) >= Omega(N log N/(log log N)^2).
In particular the average and hence the maximum of E+U over those cuts are Omega(log N/(log log N)^2). This holds unconditionally as a statement about the partial map; under finite twins U corresponds to infinite rays without a later reentry rather than termination. If all sufficiently large roots return then U is bounded and E alone has unbounded maxima, quantitatively of this order. The statement is an average over cuts, not a lower bound for every individual X. It is equivalent to integrating the previous truncated mean-gap lower bound and provides the exact crossing-edge formulation. It is not a contradiction to a bound E=o(X/log X).

## 6. Diagnostics and implications

[Audit 0372f73](https://github.com/tara-sooo/A166944-Lean/blob/0372f73dbdd538d2dcaeec93a1ef2e137a2ac6e6/research/min_direct_first_return_collision_audit.mjs), blob 82c59fd008648f6b631ce7ba293e0f462f04cbfa, exact remote readback. Run node research/min_direct_first_return_collision_audit.mjs. Actual ECMAScript execution in tool runtime, not separate Node process. Exhausted 4,866,015 residue classes for T2/4/6, all exact edge counts, indegrees and balance identities above. Constructed actual CRT stars for prime sets (13,61), (61,241,421), (61,241,421,601), with additional target clock primes71,431,613. Explicit 2-star target M128689370543643040024610431 (27 digits), predecessors M-6 and M-30. Three-star target174 digits and four-star target253 digits, exact full decimal values and moduli emitted by audit. All 1056 literal BigInt GCD ticks across all nine predecessor paths, 719 CRT neighbor-residue checks, and target eligibility checks passed. The explicit finite prime sets satisfy the same exclusions but need not follow the stronger sufficient inductive prime selection recipe. Initial trial choices of primes had empty allowed residue sets, detected by the CRT check; replaced by the above valid sets. The theorem for arbitrary k is by the constructive argument, not by extrapolating the three examples.

The earlier idea of proving C(X)=o(X/log X) to contradict the prime-source bound cannot work: actual C(X)=Omega(X) even without finite twins. Similarly a uniform bound on crossing edges is impossible if all roots return. A direct contradiction would need a different invariant, such as a constraint on an entire merged forward trajectory or on the attainable terminal basins; the local star construction does not imply such an invariant. No bound excluding the nonreset infinite branch, no twin proof, no Lean kernel verification. Main and sibling branches unchanged.
