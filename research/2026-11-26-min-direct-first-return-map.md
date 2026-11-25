# Canonical first-return map: prime source vertices, exact cylinders, and a divergent waiting tail

Continuation of [123bbd4](https://github.com/tara-sooo/A166944-Lean/commit/123bbd4a35c8c6f80ef170e7cb73085e7795d50c), on the independent direct-arithmetic branch. The purpose is to study the deterministic increasing map on ordinary canonical starting states, rather than classify individual cofactors. New results are an incoming-root obstruction, exact finite residue graphs for bounded returns, and a quantitative heavy tail for first-return gaps. No contradiction with finite twins has yet been obtained; paper proofs, not Lean kernel verification.

## 1. Definitions and terminal convention

Canonical root M odd>=5 means (t,H)=(M+2,2M-2). A reentry is a later state of this form (with root M'>M). The actual first-return partial map F(M)=M' is defined when this reentry occurs in the continuing adaptive event process. As in the previous note, quiet ticks on a stopped terminal plateau are not counted in F. Define also F*(M) by formally continuing unit ticks on a terminal plateau; it can include a final quiet reentry there. These definitions coincide on every infinite ray, and under finite twins for all M beyond the last twin center. Every first-return gap k=F*(M)-M is positive even; the elapsed ticks are exactly k and horizon gain exactly 2k. A root cannot reenter without a nonunit event, because its original H is constant only until the first such event and the canonical time for that H is unique.

## 2. Prime source vertices

Suppose M>=13 is reached from a strictly smaller canonical root, even allowing the formal quiet continuation. If the reentry occurs at an event tick n=M+2, n is odd, so its label p divides n-2=M. Eligibility p^2<=H_pre+1<2M implies p<M, since M>=13. Thus an event-tick reentry target is composite.

Otherwise consider the last event before the canonical tick n=M+2, with unchanged final H=2M-2. Its ordinary post deficit is one of 0,2,4 because the event occurs strictly before n and the envelope is nonnegative. The previous note excludes 2 and4 at every event, hence it is 0, and the event occurs at t=M-1, even. Its label p divides M-1. The next three ticks must all be quiet. By the seven-tick normalization rule at H>=24, this is possible precisely when H!=2 mod3 and H!=1 mod5, i.e. M!=2 mod3 and M!=4 mod5.

Consequently every prime M>=13 satisfying
    M=2 mod3 OR M=4 mod5
has indegree zero for F and F*, even allowing arbitrarily long earlier canonical trajectories. No canonical ancestry can evade the obstruction. Infinitely many such primes exist already by the elementary Euclid argument for primes 2 mod3: if a finite list exhausts them, 3 times their product minus1 has a prime divisor 2 mod3 outside the list. The obstruction occupies five of the eight reduced residue classes mod15 (2,4,8,11,14). Optional use of the classical prime number theorem in fixed arithmetic progressions yields asymptotically (5/8) of all primes as certified sources; that standard stronger counting theorem is not needed for the incoming obstruction or infinitude.

Conversely a prime M>=13 not satisfying either excluded residue admits an abstract predecessor of the formal canonical state: p=3, start (M-2,2M-4), next even tick M-1. Since M=1 mod3, gcd(M-1,2M-5)=3 (the gcd divides3 and is divisible by3), and 3 is eligible. The resulting H=2M-2 is even reset, and exactly the next three ticks are quiet. The start obeys the envelope. This is an abstract one-event predecessor, not a proof that a smaller canonical root reaches that start. The criterion therefore exactly distinguishes forbidden vs possible abstract last-event entry for these prime targets, but the actual image of F can be smaller. If the resulting plateau is terminal, the converse is for F* or virtual continuation only.

Also an excluded prime source has a short first wait: M=2 mod3 makes H+1=2M-1 divisible by3 with odd clock at relative j=4; M=4 mod5 makes H-1 divisible by5 with even clock at j=9, so the first wait is <=4 or <=9 respectively (possibly preempted).

## 3. Exact first-return cylinders

Start at M, write j=n-(M+2)>0 and let E be the horizon gain before that tick. At odd j (even absolute n) the raw gcd is
    gcd(M+j+2,2j+7-E);
at even j (odd absolute n) it is
    gcd(M+j,2j+1-E).
The second arguments are odd and nonzero; their absolute values are <=2T+7 for 1<=j<=T, from E>=0 and the envelope H<=2(t0+j-1), which gives E<=2j+4. Hence all possible labels are odd primes <=2T+7. If 2M-1>=(2T+7)^2, all such factors are eligible throughout the prefix. For such M the entire prefix through T is determined by M modulo
    P_T=product of odd primes <=2T+7,
together with odd parity. This is the previous relative-clock CRT idea specialized to first-return extraction. The condition at the end of tick j for a canonical reentry is exactly j even and E_after=2j. Thus F*(M)-M<=T and its value are completely periodic on sufficiently large odd M, of period 2P_T; otherwise the prefix has no reentry. Under finite twins the same holds for actual F on sufficiently large M. This statement is not an unconditional exact periodicity of F with its stopped-plateau convention.

Define a finite directed graph on the P_T odd residue classes mod2P_T, with an edge from residue M to M+k when its formal first return gap k<=T. Each vertex has outdegree<=1. This graph is acyclic. Indeed a directed cycle lifts from a sufficiently large odd representative to an infinite sequence of actual nonunit segments (formal quiet continuation cannot produce another edge after a terminal reentry). Each segment increases M and uses only labels<=2T+7. This contradicts the fixed-pool product barrier, since an infinite sequence of such labels cannot cross the next even multiple of their product. In particular any consecutive chain of returns with all gaps<=T has bounded length independently of its initial root, after the fixed cutoff threshold. One may compute the exact maximum length by the finite graph, rather than use its crude number of vertices. No bound on the length of a chain with unbounded gaps follows.

The audit exhausts complete residue periods for T=2,4,6; the deliberately safe period includes some unused primes. P_T=1155,15015,4849845 respectively. Exact counts:
    T=2: no return1001, gap2 154; maximum consecutive edges1.
    T=4: no return12363, gap2 2002, gap4 650; max edges2.
    T=6: no return3539795, gap2 646646, gap4 209950, gap6 453454; max edges4.
Here the no-return category is only through the specified T, not permanent nonreturn. For example the exact density of gap2 is 2/15. The graph counts refer to large-root cylinders F*, not empirical proportions of bounded canonical trajectories.

## 4. Exact first-wait tail

Let W(M) be the first nonunit waiting time, infinity on an initially terminal plateau. For every odd prime p define j_+(p) as the least positive odd j with 2j+7=0 modp, and j_-(p) as the least positive even j with 2j+1=0 modp. The first clock time from a root with p dividing H-1=2M-3 or H+1=2M-1 is respectively j_+ or j_-, as long as no earlier event occurs. Eligibility at the initial H is understood. Direct solution gives for p=1 mod4, j_+=(p-7)/2 (add 2p if nonpositive) and j_-=(p-1)/2; for p=3 mod4, j_+=(3p-7)/2, j_-=(3p-1)/2. These are positive with the required parity (including p3 and p5).

For fixed T and sufficiently large roots so all p<=2T+7 eligible, W(M)>T iff for each p the root avoids M=3/2 modp when j_+(p)<=T, and avoids M=1/2 modp when j_-(p)<=T. The two residues are distinct. Put rho_T(p)=1_{j_+<=T}+1_{j_-<=T}. Then the exact density among odd roots is
    delta_T=product_{odd prime p<=2T+7}(1-rho_T(p)/p)>0.
All primes <=(2T+1)/3 have both clocks by T for sufficiently large T (the small p5 wrap is included once T>=9); no p>2T+7 can hit. Therefore
    product_{3<=p<=2T+7}(1-2/p) <=delta_T
    <=product_{3<=p<=(2T+1)/3}(1-2/p).
These products are Theta(1/log^2 T). For a self-contained order estimate, use log(1-2/p)=2log(1-1/p)+O(1/p^2) with summable error. The earlier four-residue sieve note proved sum_{p<=x}1/p<=log log x+O(1) from Chebyshev theta(x)=O(x), partial summation and the Euler product at 1+1/log x; this gives product(1-1/p)>=c/log x. The reverse bound follows from product_{p<=x}(1-1/p)^(-1)>=sum_{n<=x}1/n>=log x. Omitting p2 changes only a constant. Hence
    delta_T=Theta(1/log^2 T).                         (1)
No independence assumptions on prime neighbors or PNT needed. In particular this is not a probabilistic model of the MIN dynamics. For T=2,4,6 the exact counts of quiet residues are616/1155,3696/15015,1029952/4849845, as verified by exhaustive CRT periods.

## 5. Growing-scale consequence and divergent truncated return mean

For N large choose T=floor(log N/(32 log2)). Chebyshev theta(x)<=4(log2)x gives P_T<=exp(4 log2*(2T+7))=O(N^(1/4)). The cutoff threshold (2T+7)^2 is much smaller than N. Among odd M in [N,2N], complete residue periods of length P_T in the odd enumeration and an incomplete remainder give
    # {M odd in [N,2N]: W(M)>T}
       >= delta_T*(N/2-O(1))-O(P_T)
       =Omega(N/(log log N)^2).                      (2)
Set return gap R(M)=F(M)-M when defined, infinity otherwise, even if termination precedes any reentry. Then R(M)>=W(M) with the convention that a terminal initial state has W=infinity. Hence
    (1/#odd roots in [N,2N])*sum_{M odd in [N,2N]} min(R(M),T)
       >= Omega(log N/(log log N)^2).                 (3)
The estimate also holds with F*. Under finite twins all roots in these intervals are on infinite rays for sufficiently large N. If all such roots return, (3) is an unconditional lower bound on their actual finite average return gap, which diverges with N. If some never return the truncated version still applies, without pretending they have a finite gap. This is stronger than merely saying that a bounded-gap chain cannot persist: a quantitatively large collection of roots has intrinsically long first waits.

Another consequence under finite twins: each of the roots counted in (2) remains at its initial H=2M-2 for at least T ticks. Over integer times [N+2,2N+T+2], their total occupancy is at least T times the count in (2). At a common absolute tick, different such roots have distinct horizons. Thus at some common tick in this range at least Omega(log N/(log log N)^2) different live trajectories are simultaneously still on their distinct initial plateaus. This is a statement about simultaneous states, not about eventual nonmerger: they may later coalesce.

## 6. Exact graph balance under finite twins

Fix an odd lower cutoff M0 beyond the last twin center (conditional), and take all odd roots M0<=M<=X. For the induced directed graph of F, let S(X) be the number with zero incoming edges from this set, C(X)=sum_{v} max(0,indegree(v)-1), E(X) the number of roots whose defined F(M)>X, and U(X) the number where F is undefined (no later root on their infinite ray). Counting the internal edges in two ways gives
    S(X)=C(X)+E(X)+U(X).                              (4)
Indeed number of internal edges = number of vertices - E-U, and also number of vertices - S + C. Every forbidden prime target is counted in S. Thus infinitely many certified sources force at least one of cumulative collision excess, number of crossing return edges, or number of never-returning roots to be unbounded as X grows. Optionally using PNT in fixed AP, S(X)>=(5/8-o(1))X/log X, so at least one of those three terms is Omega(X/log X) for each large X. No assumption that the same term dominates every window. If all roots return and the gaps obey F(M)-M=o(M/log M) uniformly for sufficiently large M, then E(X)=o(X/log X) (split the finitely many early roots, all other crossing roots lie within o(X/log X) of X), and (4) forces C(X)>= (5/8-o(1))X/log X. This last conditional result is about actual canonical reentry merges, not the historical merger evaluation framework. Increasing maps need not be injective, and both infinite return chains and rootless infinite paths remain possible; (1)-(4) do not imply twin infinitude.

## 7. Diagnostics and persistence

[Audit 3e94875](https://github.com/tara-sooo/A166944-Lean/blob/3e948752a28f6b9c71359266cfbe360a05367038/research/min_direct_first_return_map_audit.mjs), blob b84f4a4eefe56a68da7165879b4b9e3b1d07bad4. Exact remote readback. Run node research/min_direct_first_return_map_audit.mjs 200000 180. Actual ECMAScript execution in tool runtime (not separate Node process). 4,866,015 full residue evaluations for T=2,4,6, with exact quiet product and graph acyclicity/depth checks. For all odd roots13..200000 up to first actual reentry, termination or180 nonunit events: 99,994 roots, 669,213 processed events, 72,315 actual reentries, 27,656 terminal before return, 23 unresolved by cap, 11 defined edges crossing upper bound. 11,232 forbidden prime source roots, zero incoming among them; 3,487 prime-target reentry incidences, all allowed residue classes. 6,747 abstract prime predecessor checks, 99,994 exact first-wait comparisons, 26,846 short actual/formal gap comparisons, maximum observed defined gap646. Graph balance for known edges: zero indegree64945, collision excess37255, crossing11, terminal27656, unresolved23. Counts are bounded-scan diagnostics, not claims that U or C have those asymptotics. Example forbidden source M23 returns to25, so source does not mean terminal. The audit field sourcePrimeReentries is an unused zero-initialized counter; the actual source exclusion is enforced by the incoming-target assertion and final indegree loop. No new large-window trajectory or Lean verification. Main/sibling branches unchanged.

Next: investigate whether the exact first-return map can have arbitrarily long chains of increasing prime/composite roots while respecting its source constraints, or derive a stronger upper bound on collision excess/large crossing excursions. The mean-gap theorem constrains the family of all roots rather than the time average on any one path; confusing those averages would be invalid.
