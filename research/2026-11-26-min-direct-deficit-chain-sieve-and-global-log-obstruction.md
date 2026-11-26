# Higher-dimensional deficit-coordinate chains and a stronger global logarithmic obstruction

Continuation of [59b68e7](https://github.com/tara-sooo/A166944-Lean/blob/59b68e78791eef09c59d64cc35876fb4403e32bf/research/2026-11-26-min-direct-uniform-deficit-range-and-global-precursors.md). Return to its cumulative variation argument, but count close chains of several events together rather than separate pairs. Under absence of a large twin-cofactor witness, five consecutive close long nonresets in a factor-two square-root band have distinct deficit coordinates. The corresponding prime lines admit a fixed-dimensional sieve, with the multiplier sum controlled by an exact gcd/lcm decomposition. Crucially only the FIRST relay displacement is needed in the counting, since an actual selected list on one ray uniquely determines its continuation. This strengthens the global logarithmic obstruction in this band-restricted regime. It is not an upper supply theorem for the original small/middle crossing populations or a proof of twin infinitude.

## 1. Close-chain reduction and distinct coordinates

Fix lambda>1, Y=lambda X, C=floor sqrt(Y+1), a physical contiguous event block with pre-horizons in [X,Y] on a fixed canonical ray. Fix eta>0, and an integer lower threshold T defining a label band [T,2T), where eta sqrt X<=T<=C (the band may vary between blocks). Choose an arbitrary subset of nonreset events p in the band and p<=C. At each event with side I, e=1-2I, wait w and ordinary post deficit d', write x=(d'-6I)/2=hp>0. Assume for the local counting theorem
    x <= K X^(1/2+delta0),    0<delta0<1/10,             (1)
with fixed K, delta0. This is enough to have x<T^2 for large X, so each selected x has a unique prime factor >=T. No clock length, prime cofactor or crossing restriction is imposed on the chosen population.

Order the selected visits physically. Consecutive visits have relay E=H2-H1-(p1-1), post difference v=d2'-d1', adjusted-coordinate difference c=v/2-3(I2-I1). Join them by a close edge when E<=B and |v|<=A, with A,B nonnegative integer cutoffs. In what follows take A,B=log^O(1) X (with any fixed exponents), so eventually
    A+5B <= (T-1)/2,    4B<T,    4(floor(A/2)+3)<T/2.
The actual drift across the intervening events is at most 5E, hence the successor on every close edge has 4w>=p-1 by the previous automatic-long lemma. Since p>=T is of square-root scale, its cofactor q=(H-e)/p is prime by the cube threshold certificate. Its wait exceeds 6 and H=0 mod3. Only the first vertex of a maximal close-edge component may be uncertified. The first vertex of the component will not be used in the j-window counts below.

For fixed j in {3,4,5}, consider any j successive selected visits within a close component, starting at its second or a later vertex. All j are long and prime-cofactor certified. Suppose two of them have identical x. Because x<T^2, their label p is identical, and their adjusted D=2x is identical. The earlier same-adjusted-stratum spacing lemma says their increasing odd cofactors q1,q2 either differ by 2 (a twin pair), or q2-q1>=10. For clarity, w>6 implies H=0 mod3, so for the same selected label each side fixes q mod3. Equal D fixes the parity of (q+1)/2+h, hence q mod4 on each side. On the same side the difference is a positive multiple of12; on opposite sides it is 2 mod4 and one of the two nonzero even residues mod6. The only positive difference below10 consistent with both constraints is 2. This proof does not require them to be consecutive occurrences of that label.

But their physical pre-horizon span is at most
    (j-1)(2T-1+B) <= 8T-4+4B < 9T-4,
since between successive selected visits the gain is p-1+E and each p<2T. If the same p>=T recurs with q gap>=10, that span is >=10p-2>=10T-2 by H=pq+e, contradiction. Therefore if any such j-window contains a repeated x, it directly gives a certified twin pair q,q+2, q>=T. Under finite twins, this is absent for sufficiently large X. Equivalently every eligible j-window has j distinct coordinates. Equal x implies equal label, but the reverse need not hold: occurrences of the same label with DIFFERENT x are allowed at nonadjacent positions. We will require only distinct coordinates and distinct FIRST TWO labels: the latter holds for a close edge because any same-label return needs E>=p-1. No assertion that all j labels are distinct is needed for the sieve.

## 2. A fixed-dimensional prime-line sieve with a bounded-ratio multiplier sum

Let R_x be the range of the selected x, W=max(T,R_x+1). Count starting coordinates x of distinct-coordinate j-windows with offsets
    c_1=0, c_i=x_i-x_1,  |c_i|<=(j-1)(floor(A/2)+3).
There are O_j((A+1)^(j-1)) offset lists. Keep only lists of pairwise distinct c_i. We count all necessary arithmetic possibilities for x and the positive multipliers h_i with p_i=(x+c_i)/h_i prime in [T,2T), subject to (1) for each coordinate. For a fixed offset list, if L=min selected x>=W, all starting x lie in [L,L+W-1]; since the offsets are o(T) and L>=T, all h_i lie in a bounded-ratio interval [L/(4T),3L/T], and h_i<=K X^(1/2+delta0)/T=O_(K,eta)(X^delta0).

For a fixed h-vector, the simultaneous congruences x=-c_i mod h_i are either incompatible or give one residue class x0 modulo P=lcm(h_1,...,h_j). Necessarily
    gcd(h_i,h_k) | (c_i-c_k)
for every pair. Put x=x0+Pz. The j required prime forms are
    L_i(z)=(P/h_i)z+(x0+c_i)/h_i.
For distinct offsets their pairwise determinants equal
    (P/(h_i h_k)) (c_k-c_i)
and are nonzero integers. The product of these determinants and the positive slopes is a nonzero integer of size X^O_j(1), since all data, including offsets, are polynomially bounded. For primes f>j not dividing that product there are j distinct forbidden residues in z. At exceptional primes omit the restrictions. By the fixed-dimensional Selberg argument from [9e3203a](https://github.com/tara-sooo/A166944-Lean/blob/9e3203a1b5c380f1a5b8b3328cddd230a86a7f05/research/2026-11-26-min-direct-repeated-cofactor-cluster-sieve-and-stratum-capacity.md), the count on N consecutive progression parameters is
    O_j(N (loglog X)^j / log^j(2N)).
The discriminant factor is O_j((loglog X)^j) by splitting its prime divisors at log X; the omission of the finitely many primes <=j is harmless. In this application N can be padded to ceil(W/P)+1. As P<=prod h_i=O(X^(j delta0)), W>=T>>sqrt X and j delta0<1/2, the padded interval is polynomially long. The sieve cutoff floor N^(1/12) is below the candidate primes >=T. Thus the bound for a compatible h-vector is
    << W/P * (loglog X)^j/log^j X.                     (2)
This sieve does not require the actual labels to be pairwise distinct: distinct c_i guarantee nonproportional prime forms, which is the relevant condition.

To sum 1/P over multiplier vectors without a factor growing like X^delta0, fix all pairwise gcds g_ik=gcd(h_i,h_k). Every g_ik is a positive divisor of abs(c_i-c_k). Define
    d_i=lcm_(k!=i) g_ik,   u_i=h_i/d_i,   D=lcm_i d_i.
Prime by prime, if one h_i has strictly maximal valuation, d_i has the second-largest valuation and u_i carries the difference; if the maximum is shared, no u_i carries that prime. Thus the u_i are pairwise coprime and the exact identity is
    P=D prod_i u_i.
For this fixed gcd matrix the h_i are in a common bounded-ratio interval, so each u_i is in an interval with the same bounded ratio. Dropping all remaining consistency constraints in the positive sum gives
    sum_(h-vectors of this matrix) 1/P
       <= (1/D) prod_i sum_(u_i in its interval) 1/u_i
       = O_j(1).
The number of matrices is bounded by prod_(i<k) tau(abs(c_i-c_k)), where tau is the divisor-count function. The elementary bound tau(n)<<_epsilon n^epsilon for every epsilon>0 (choose the finitely many small prime factors separately) therefore gives, for every fixed epsilon>0,
    sum_(compatible h-vectors) 1/P <<_(j,epsilon) (A+1)^epsilon. (3)
Here epsilon has been divided by the fixed number of pairs before applying the divisor estimate. This controls even nontrivial gcds, rather than incorrectly replacing P by the product of all h_i. It is uniform in the actual baseline deficit.

If L<W, cover possible first x in [T,min(2W,K X^(1/2+delta0))] by dyadic shells [S,2S), starting at S=T. In each shell h_i are in [S/(4T),3S/T] and have the same global upper cap. Parameter lengths S/P are polynomially large since S>=T. Apply (2)-(3) with S in place of W; sum the shell widths O(W). Thus in both cases the number of distinct-coordinate prime-line candidates (counted with multiplier vectors if needed) for a fixed offset list is
    << W (A+1)^epsilon (loglog X)^j/log^j X.            (4)

## 3. The first-pair CRT is enough: avoid enumerating later relays

For fixed x and offsets c_i, each x+c_i<T^2 determines at most one eligible large prime p_i. In a close chain the first two labels p1,p2 differ, and for a fixed first relay E1<=B and first two sides the necessary horizons obey
    H1=e1 mod p1,
    H1+p1-1+E1=e2 mod p2.
The modulus p1*p2>=eta^2 X. Consequently there are O_(lambda,eta)(1) possible first horizons H1 in the whole block. On the FIXED selected list of one actual monotone ray, a first H1 specifies at most one actual starting event and exactly one subsequent j-window, if it exists. We do not need to enumerate later relay gains E2,...,E_(j-1) or later sides to obtain an upper bound. They may be arbitrary subject to the close-edge hypothesis. This saves (B+1)^(j-2) relative to counting complete relay words. It is not an assertion that arithmetic candidates have unique trajectories across different roots.

Let F_j be the total ENDING-event gain of the eligible j-windows starting at the second or later vertex of their close components. Each ending gain <=C. Under absence of a direct twin witness, all their offsets are distinct by section 1. Combine (4) with the O_j((A+1)^(j-1)) possible offsets, at most B+1 first relay choices, and four first-pair side choices:
    F_j << C W (B+1)(A+1)^(j-1+epsilon)
                   * (loglog X)^j/log^j X,              (5)
for each fixed j=3,4,5, fixed epsilon>0, with constants depending on lambda,eta,K,delta0,j,epsilon. This is the new high-dimensional close-chain supply bound. It holds uniformly for arbitrary filtered nonreset populations satisfying (1). It has no fixed multiplier cap; the power cap (1) ensures the parameter intervals stay long. If a twin witness does occur the bound is not asserted for the repeated-coordinate windows; the witness is itself the alternative.

## 4. Cover the complete selected population by chains and exceptional relays

Let F be total chosen gain, U_out=G-F, V_d the total absolute ordinary deficit variation on the full physical block. The number b_bad of nonclose edges is at most
    U_out/(B+1)+V_d/(A+1)
by the disjoint relay and post-to-post budgets. There are b_bad+1 close components, counting singleton components. A component of n<=j vertices contributes at most j C. If n>=j+1, it has exactly n-j eligible j-windows starting at its second or later vertex. Each ending gain >=T-1, and each component gain per vertex <2T-1, so its entire gain is at most
    2(j+1) times its eligible ending-window gain,
because n<=(j+1)(n-j) and (2T-2)/(T-1)=2 for integer p<2T. The windows' ending vertices are distinct within that component. Hence under absence of a witness
    F <= 2(j+1)F_j
         + j C [1+U_out/(B+1)+V_d/(A+1)].              (6)
This is a physical gain budget; no recurrence-state probability or uniform mixing assertion is involved. It allows arbitrary numbers of short close components, and pays them via the actual bad-edge budgets.

For example if F>=rho X with fixed rho>0, put z=C U_out/X, y=C V_d/X, u=R_x/T. Suppose z,y,u are polylogarithmic. Choose A=ceil(K0 y), B=ceil(K0 z) with sufficiently large fixed K0 depending on rho,j; these satisfy the close assumptions. Since CW=O(X(1+u)), (5)-(6) imply the necessary condition
    (1+u)(1+z)(1+y)^(j-1+epsilon)
       >> (log X/loglog X)^j.                         (7)
This conclusion is conditioned on absence of the actual twin witness, not on finite twins for all x. Compare the pair product in the previous deficit-coordinate theorem: here the higher power of the variation budget is accompanied by the j-th power of the sieve saving, whereas the relay budget still occurs only once. When U_out and V_d have similar size, this gives the exponent j/(j+1+epsilon) after R_x<=V_d/2+3. In some strongly unbalanced budget regimes the older pair estimate can be stronger; we do not replace it universally.

## 5. Global accumulation: improve the infinitely-often exponent in a factor-two band

Assume a hypothetical infinite canonical ray from a fixed root and finite twin primes. Put X_i=16^i X0 and split it at first plateaus reaching these horizons as in the preceding note. For each physical block i choose ANY subset of nonresets with p in a band [T_i,2T_i), T_i>=eta sqrt X_i, T_i<=C_i; allow T_i and the selected list to vary between blocks. Let U_i be the full complementary gain (including all other label bands and resets), V_i the full ordinary variation. Then for every fixed 0<gamma<5/6,
    limsup_i (U_i+V_i)/(sqrt X_i (log X_i)^gamma)=infinity. (8)
In particular infinitely many scales have U_i+V_i >= sqrt X_i (log X_i)^gamma. This is an improvement over the earlier exponent 2/3 when using this factor-two population, not a result for all the earlier square-root populations with unrestricted band width.

Proof. If the limsup is finite, for some fixed K2 eventually U_i+V_i<=K2 sqrt X_i log^gamma X_i. Thus F_i=G_i-U_i>=X_i and, by summing actual ordinary variation from the canonical prefix and using sqrt X_(i-1)=sqrt X_i/4,
    d <= O_fixed_prefix(1) + (4/3)K2 sqrt X_i log^gamma X_i
at every plateau in block i. All chosen coordinates satisfy (1) with K=1 and any fixed delta0 in (0,1/10), for sufficiently large i. R_x<=V_i/2+3 and W=O_(eta,K2)(sqrt X_i log^gamma X_i). Pick epsilon>0 small enough that (6+epsilon)gamma<5. Use j=5, A=B=ceil(K3 log^gamma X_i) with a fixed K3 large compared to K2 and the gain-cap constants. In (6) the bad-edge term can be made <X_i/2 eventually. The close-window upper bound (5) is
    O(X_i log^((6+epsilon)gamma-5) X_i (loglog X_i)^5)
      = o(X_i).
For sufficiently large i the finite-twin assumption excludes all possible q,q+2 with q>=T_i, so (5)-(6) apply to every chosen block. This contradicts F_i>=X_i. The same argument with j=3,4 gives gamma<3/4,4/5 respectively, but j=5 is strongest within this range. If the hypothesis of a factor-two band dominating gain fails, U_i may be macroscopic and (8) then holds trivially. No dominance of a single band, small budgets, or actual high upward supply has been forced.

The result adds a stronger global necessary condition to the three-scale alternative of the previous notes, but leaves the small/middle crossing supply and macroscopic positive-variation branch open. In particular the logarithmic bound remains submacroscopic. Further progress requires an upper supply constraint at a comparable scale, or a forcing mechanism for an unbounded direct twin witness. Merely increasing the number of prime lines without controlling repeated coordinates or their offset budgets would not justify a further exponent improvement.

## 6. Diagnostics and preservation

[Final audit 7a821ba](https://github.com/tara-sooo/A166944-Lean/blob/7a821ba18fb0d80615ca4818d8c47559fc83a546/research/min_direct_deficit_chain_sieve_audit.mjs), blob f62420275c9f2fbf4ce7eb0f9caea920a7237217. Exact remote readback. Run node research/min_direct_deficit_chain_sieve_audit.mjs 60000. Actual ECMAScript executed in tool runtime, not a separate Node process. 29998 odd canonical roots through60000,549085 actual MIN events,0 cap180 unresolved. 34821 nonempty finite band controls T17/31/61,72197 selected incidences,37376 filtered edges,475 close edges all automatically long,71722 components,104463 cover and gain-budget checks for j3/4/5. No eligible j-window starting after the first vertex of a close component was found in this strict finite scan. Thus actual multiwindow CRT, witness and nontrivial component tests have ZERO coverage; the actual controls exercise the edge and short-component budgets, not a realized five-event chain. The analytic proof does not claim that such chains are forced without the small-budget assumptions.

Independent abstract controls (not claimed MIN trajectories):18268 compatible distinct-offset congruence systems,16135 with a nontrivial multiplier gcd,99 further prime tuples;18367 exact progression/parameter checks,113997 gcd/lcm and determinant checks,114063 small-prime residue tests. 30000 synthetic component cover controls including53281 nontrivial long-component weight checks.4858 same-adjusted-stratum residue and prime-spacing controls,568 twin gap incidences,4290 non-twin spacing incidences. All final assertions passed. Earlier fixed-dimensional Selberg proof used analytically; finite tests do not establish the asymptotic constant or infinite-ray existence. No Lean executable/kernel verification or external novelty claim. Main and sibling branches not modified.
