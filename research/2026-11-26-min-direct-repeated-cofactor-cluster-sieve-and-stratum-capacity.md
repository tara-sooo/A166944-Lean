# Higher-dimensional sieve for repeated cofactors and near-flat stratum capacity

Continuation of [074993c](https://github.com/tara-sooo/A166944-Lean/blob/074993ce8fa710aea5f38060ec52ab4a1a28fca8/research/2026-11-26-min-direct-crossing-clock-and-factor-hierarchy.md). The previous certified long-clock population has a dimension-two upper sieve for each selected prime. Here a cluster of j repeated occurrences of one selected prime gives 2j distinct linear forms, leading to a stronger short-return supply bound. Separately, combine the older mod-3/equal-adjusted-deficit spacing with the factor hierarchy to obtain an explicit twin witness criterion in a narrow tube of very few ordinary deficit values. These are new restrictions on the remaining certified population, not a proof that it is absent. Paper deductions and finite diagnostics; no Lean kernel verification or external novelty claim.

## 1. Repeated cofactor patterns

Retain the actual adaptive MIN model. Let a block of a fixed canonical ray have pre-horizons in [X,Y], Y=lambda X for fixed lambda>1, total gain G=O(X), label cap C=floor sqrt(Y+1). A long event has 4w>=p-1; every factor of H+-1 is >=w/2>=(p-1)/8. Use any of the previous thresholds T_k=max(256ell+1,1+ceil(9(Y+1)^(1/k))), k=3,4,5,6, ell=ceil(P_R^(4/11)) at the balanced primorial cutoff. The selected cofactor q=(H-e)/p is odd, >=p, and for p>=T_k both q and pq+2e have no prime factor <=(Y+1)^(1/k). At k=3, q is prime. The following sieve does not require q itself prime and applies to any selected subset of these long events, including only actual surviving-cut crossers.

Fix p, and order the selected events with label p by their physical position. Their q values strictly increase, since the pre-horizon grows by >=p-1 between them and e changes by at most2. Let j>=2 be FIXED, and select a pattern of j successive visits in this filtered p-list, having q_i=q+a_i, a_1=0, 0<a_2<...<a_j, all a_i even. For a short cluster require each half-gap (a_(i+1)-a_i)/2<=K, K a positive integer. There are at most K^(j-1) possible offset patterns and 2^j possible sign lists e_i. Only patterns with a_j<= (Y+1)/p need consideration.

For each pattern the 2j linear forms in the initial q are
    L_i(q)=q+a_i,
    M_i(q)=p(q+a_i)+2e_i.
Every form must avoid all sufficiently small prime divisors. Put nu=2j and let Delta be the absolute product of determinants A_i B_h-A_h B_i of all unordered pairs of forms A q+B. The determinants never vanish: within L forms the offsets differ; within M forms the difference p(a_i-a_h)+2(e_i-e_h) cannot be zero for distinct even offsets and p>=5; between L and M forms a nonzero constant +/-2 cannot equal an integer multiple of p. In particular Delta is a positive integer <=X^{O_j(1)} uniformly for all relevant patterns (and fixed lambda). For any prime f>nu, f<p, f not dividing Delta, there are exactly nu DISTINCT forbidden residues modulo f. At exceptional primes there are at most nu, still <f. This is an actual arithmetic condition on the same q across its repeated visits, not a probabilistic independence model for events.

## 2. Elementary higher-dimensional sieve with a uniform discriminant factor

Here is the needed extension of the [dimension-two upper sieve](https://github.com/tara-sooo/A166944-Lean/blob/074993ce8fa710aea5f38060ec52ab4a1a28fca8/research/2026-11-26-min-direct-global-sieve.md). Fix nu. On N consecutive integers let the primes nu<f<=z have forbidden sets of size rho(f)<=nu, with rho(f)=nu whenever f does not divide a given positive integer Delta. For the application each rho(f)>=1. Assume z<p and below the certified factor threshold. Write rho(d)=prod rho(f), g(d)=rho(d)/d, h(d)=prod (1-g(f))/g(f), on the squarefree products d of these primes with d<=z; at d=1 use value1. If any rho(f)=0 simply omit that prime. The set is divisor-closed. The Selberg quadratic diagonalization and divisor inversion from the earlier note are unchanged:
    G(z)=sum_{d<=z} 1/h(d),
    S(I,z)<=N/G(z)+z^6.                                    (1)
Indeed weights lambda_d with lambda_1=1 and quadratic minimum 1/G exist by the earlier explicit inversion. The bound abs(lambda_d)<=prod_{f|d}(1-rho(f)/f)^(-1)<=d follows since rho(f)<f and rho(d)<=d. The same CRT interval errors and sum_{d<=z} d^2<=z^3 give z^6. No constant depends on the translation of the interval.

For the lower bound on G, keep only generic primes nu<f<=y=z^eta not dividing Delta, where eta>0 is a sufficiently small fixed constant depending on nu. On the complete product of these primes the total weight sum of 1/h is
    W=prod (1+nu/(f-nu))=prod (1-nu/f)^(-1).
Normalize these weights on squarefree subsets. Inclusion of a given prime has weight-probability nu/f, so the weighted mean of log d is nu sum_{f<=y} log f/f=O_nu(log y) by Chebyshev and partial summation. Choose eta small enough that this is <=.5 log z for large z. Markov gives at least W/2 weight on d<=z; those terms occur in G. Mertens' product (or its elementary order bounds) and the convergent O_nu(sum f^-2) correction then give
    G(z) >>_nu (log z)^nu / J_nu(Delta),
    J_nu(Delta)=prod_{f|Delta, f>nu prime}(1-nu/f)^(-1).    (2)
To see the uniform discriminant bound for Delta<=X^{O_j(1)}, split f<=log X and f>log X. The former product is O_nu((loglog X)^nu) by Mertens; for the latter there are at most O_j(log X/loglog X) factors, each log contribution O_nu(1/log X), so their product is bounded. Thus
    J_nu(Delta) = O_j((loglog X)^(2j)).                    (3)
There is no assumption on the prime factorization of Delta beyond its size.

Take z=floor N^(1/12). In the application N<=O(Y/p)+O(1), and this z is below both p and the factor threshold for every k=3..6 for sufficiently large X. The error z^6<=sqrt N is absorbed by the main upper bound with a larger constant; small N is handled by increasing the constant depending only on j. Equations (1)-(3) give the uniform estimate
    S(I,z) <<_j N*J_(2j)(Delta)/log^(2j)(2N)
           <<_j N*(loglog X)^(2j)/log^(2j)(2N).           (4)
The full singular factor version is available when its actual value is smaller. All constants are allowed to depend on fixed lambda and j. This proof of the truncated Euler-product lower bound is for a fixed dimension, not a growing j sieve.

## 3. Short-cofactor cluster supply on one physical ray

For a physical contiguous subblock B of horizon gain L, each first cofactor q at fixed p lies in an interval of at most N=ceil((L+2)/p)+1 consecutive integers, because the two side corrections differ by at most2. For a fixed pattern/sign list each possible q determines at most one actual starting event on a monotone ray. Count every qualifying j-window of successive visits in the filtered p-list by its start. Summing (4) over the at most 2^j K^(j-1) patterns gives, in units of gain p-1 per starting window,
    W_(p,j,K)(B) <<_j
      K^(j-1) * (L+p) * (loglog X)^(2j)
                         / log^(2j)(2+L/p).               (5)
Here all j visits must lie inside B. This allows arbitrary intervening events of other labels or even unselected events of p. It is an upper bound on actual starts, not on all sequences of q in the integers with arbitrary multiplicity. For the whole macroscopic window L=G=Theta(X), log(2+L/p) comparable to log X, hence
    W_(p,j,K) <<_j X K^(j-1) (loglog X/log X)^(2j).         (6)
The previous dimension-two marginal gain bound corresponds to j=1; the j>=2 case constrains repeated short-gap clusters, not arbitrary events.

Split the filtered visits of each p into maximal components connected by consecutive half-gaps <=K. A component of size n>=j contains n-j+1 starting j-windows, and n<=j(n-j+1). Consequently the total gain F_(j,K) of ALL selected events belonging to components of size at least j is at most j times the sum of the starting-window weights. If the total number of selected labels is b,
    F_(j,K) <<_j b X K^(j-1) (loglog X/log X)^(2j).         (7)
Thus a macroscopic population in short repeated-cofactor clusters requires
    b >>_j (log X/loglog X)^(2j) / K^(j-1).               (8)
For K fixed and j=2,3,4 this forces respectively log^(4-o(1)), log^(6-o(1)), log^(8-o(1)) distinct selected labels, instead of the earlier marginal log^2 lower bound. More generally K<=log^a X for fixed 0<=a<2 gives exponent 2j-a(j-1)-o(1). For a population supported on at most log^B X labels, with B fixed, choose fixed j so that 2j-a(j-1)>B. Then the fraction of macroscopic gain in components of size>=j tends to zero. In this regime almost all gain must come from short components separated by half-gaps >K. The conclusion concerns the filtered actual occurrence lists, and is valid for the preceding crossing-only long population in particular.

There is also a varying-support version. On arbitrary pairwise disjoint contiguous subblocks B_i of gains L_i>=X^epsilon C, epsilon>0 fixed, choose sets of at most b labels separately in each B_i, and construct the filtered components within each B_i. In (5), log(2+L_i/p)>=epsilon log X and L_i+p<=2L_i. The sum of the L_i is at most G=O(X), so (7)-(8) apply to the total component gain with b the MAXIMUM chosen support size per block, not the size of the union of those supports. No independence or preselection of the blocks/supports is needed. For shorter subblocks the explicit bound (5) is usable but the log X denominator cannot be substituted in general.

These results do not force a macroscopic short-cluster population. A long population can have many different labels, or larger gaps between repeated cofactors. The previous marginal bound still applies to that alternative. This is a new conditional upper-supply theorem, not a contradiction merely from the existence of macroscopic certified gain.

## 4. Twin-weight spacing at one adjusted stratum

Use the exact return identities in [repeat-cofactor](https://github.com/tara-sooo/A166944-Lean/blob/074993ce8fa710aea5f38060ec52ab4a1a28fca8/research/2026-11-26-min-direct-repeat-cofactor.md). At a selected event p>=5 write d'=2n-(H+p-1), I=(1-e)/2, D=d'-6I, and U=n-2I. For two occurrences of p, q_2-q_1=2m, U_2-U_1=lp, l>=1, l=I_2-I_1 mod2, D_2-D_1=2p(l-m). At long events p>=T_k, w>6 eventually, hence H=0 mod3: otherwise 3 supplies a strict future hit within6 ticks. Put s_i=+1 or -1 representing e_i*p mod3. Then q_i=-s_i mod3. Same-side m=0 mod3, opposite-side m=s_1 mod3. If D_1=D_2, then l=m and m is even on the same side, odd on opposite sides.

Without assuming twins finite, put eta_i=1 if m=1 and 0 otherwise. The exact integer restrictions give
    m >=3+(s_1-s_2)/2-3 eta_i,
    m >=6+(s_1-s_2)/2-6 eta_i  if D_1=D_2.               (9)
These are the older residue spacing inequalities with an explicit correction for the excluded minimal-return case. The only m=1 case for long events flips s from+1 to-1. If both q are prime, eta_i=1 is a direct twin certificate. This also covers nonconsecutive physical occurrences, provided both selected events meet the stated conditions.

For an ordered list of n_p prime-cofactor visits of a fixed p in the SAME adjusted D stratum within a physical subblock B of gain L, let r_p count adjacent q-gap2 pairs in that list. Sum (9); the signs telescope, q_last-q_first>=12(n_p-1)-2-12r_p. Since H_last-H_first=p(q_last-q_first)+e_last-e_first<=L,
    12p n_p <= L+14p+2+12p r_p.                          (10)
This includes n_p=1; if n_p=0 omit the label. The term p*r_p is a weight on actual twin certificates, not on every possible prime pair. Under finite twins and q>=p tending to infinity, all such r_p=0. Without finite twins the term retains the witness rather than assuming it away. For a constant ORDINARY deficit d at all selected visits, p>=5 nonreset cannot use both sides, since p divides (d-6I)/2 and p cannot divide3. Hence D and I are fixed, m is an even multiple of3, and q gaps are >=12 WITHOUT any primality condition on q. This strengthens the elementary flat-run bound at the previous factor thresholds.

## 5. Small-deficit-alphabet capacity and a direct twin forcing condition

At any canonical plateau in the macroscopic block, the canonical envelope gives d<=6+5(H-H_root)<=5(Y+1)+6 for event endpoints including overshoot if one uses a harmless O(C) enlargement of Y. For nonreset selected p>=T_k, d' >=2p and p divides the positive integer (d'-6I)/2. At the threshold T_k>=1+ceil(9(Y+1)^(1/k)), each positive integer of the form d'/2 or (d'-6)/2 is O(Y) and strictly < T_k^k for sufficiently large Y. It therefore has at most k-1 DISTINCT prime divisors >=T_k. This direct use of the two factors separately is sharper than the earlier product bound13.

For a physical constant ordinary-deficit run of gain L, the selected high nonreset support has size <=2(k-1). By the same-side spacing above, every such label contributes at most L/12+p (even if its cofactor is not prime), so the total high nonreset gain is at most
    (k-1)*L/6 + 2(k-1) C, k=3,4,5,6.                   (11)
This local finite bound needs no sieve asymptotic, finite twins or actual crossing restriction. The previous local sieve can still give o(L) on sufficiently long bounded-support runs; (11) gives an explicit fraction and O(C) boundary error even without a growing length ratio.

Now take k=3. Let B be ANY physical contiguous subblock of gain L, and choose any subset of its high long NONRESET events p>=T_3 (possibly only actual cut crossers) whose ORDINARY POST deficits belong to a finite set A of even integers, with
    max A - min A + 6 < 2T_3.
Only the selected visits must satisfy this tube; arbitrary intervening states, high labels and resets are permitted. Every chosen cofactor q is prime by the cube certificate. For each p, the adjusted D values lie in an interval of width <2p and are positive multiples of 2p, so they are all in ONE D stratum. Let t_A be the number of DISTINCT positive members of A union (A-6). Each chosen p divides at least one of the corresponding t_A integers v/2. Each integer has at most TWO distinct prime divisors >=T_3. Thus the actual selected support size b<=2t_A. Sum (10), letting F_A denote the chosen total gain and W_twin=sum_p p r_p:
    F_A <= (b/12)L + sum_{p used}(14p+2)/12 + W_twin
         <= (t_A/6)L + (2t_A)(14C+2)/12 + W_twin.         (12)
Use p-1<=p to pass from p*n_p to gain; all counts refer to the chosen events. This is a finite twin-forcing inequality, not a statistical estimate.

For at most TWO arbitrary post-deficit values in the narrow tube, t_A<=4 and b<=8. Also for three values a,a+6,a+12, t_A<=4. For four values a,a+6,a+12,a+18, t_A<=5. Accordingly:
    F_two <= (2/3)L + O(C) + W_twin,
    F_four_step6 <= (5/6)L + O(C) + W_twin.                (13)
If for arbitrarily large X one can force a physical subblock with L/C->infinity, and either chosen gain fraction exceeds its respective bound 2/3 or 5/6 by a fixed positive amount, then W_twin>0 and an actual pair of twin primes q,q+2 with q>=T_3 is obtained. Hence that property implies twin infinitude. More quantitatively the excess gain after the O(C) endpoint charge is a lower bound on W_twin. This uses the actual prime-cofactor certificate, not merely a primality test on small finite examples.

For any disjoint family of b0 physical blocks satisfying the two-value tube condition, under finite twins their chosen certified gain is <=(2/3) times total physical gain + O(C b0). In particular if such blocks partition a macroscopic window, b0=o(sqrt X), and the chosen population supplies more than (2/3+delta)G, this contradicts finite twins. Equivalently without the twin hypothesis the partition must produce a witness. If the earlier small-crossing mass is o(X) at T_3, then U=o(X) (all gain except actual high crossers); in a window dominated by nonreset high crossers whose pre/post deficit changes are small enough that they are long, a partition of this kind would give the required high gain fraction. The existence of such a low-complexity partition is not established, and large reset gain is not covered by the nonreset tube theorem. The condition on selected post-deficit width must be retained, even if there are only two values far apart.

This gives a concrete bridge to the remaining global large-event alternative: either sufficient deficit-alphabet complexity, sufficient gain outside the narrow nonreset tubes, or the direct twin witness in (12). It does not assert the full large-event population has a small alphabet. The higher-dimensional sieve (7) and the tube capacity (12) apply to different restrictions and do not independently imply a contradiction. Further progress needs a global bound on the supply of isolated/long-gap visits, or a trajectory constraint forcing the high-gain narrow-tube regime (or exclusion of the other crossing alternatives).

## 6. Diagnostics and preservation

[Final audit b9b0640](https://github.com/tara-sooo/A166944-Lean/blob/b9b0640f5e3cf56e8836461992a9577eb7238519/research/min_direct_repeated_cofactor_cluster_sieve_audit.mjs), blob 2adca2aff354b12ba74c83a7f378c70438136f9f. Exact remote readback. Run node research/min_direct_repeated_cofactor_cluster_sieve_audit.mjs 60000. Actual ECMAScript in tool runtime, not separate Node. All 29998 odd roots through60000,549085 actual events,0 cap180 unresolved. 154451 long events with directly verified prime q,23389 repeated-label groups,38822 consecutive filtered return comparisons,3612 twin-gap incidences,35210 other gaps;14029 mod3 and1061 same-stratum corrected spacing checks. These finite events need not satisfy the asymptotic cube threshold; direct SPF primality is used to exercise the pattern and spacing arithmetic. Counts overlap between roots/controls, not distinct pairs.

124041 components across K=2,8,32,372123 component-cover checks. At K=8 actual j=2/3/4 windows 20036/3655/922;24613 pattern identities,201739 nonzero determinant checks,13051 small-prime residue checks in the actual eligible roughness ranges. 54 independent finite Selberg controls of dimension4/6/8, varying signs/offsets, translated intervals, primes p=53,101,107 and z=13,23,43;420 exact integer-scaled weights,3960 exact quadratic summands,10800 pointwise square-majorant checks,54 truncated-product lower checks. All passed. These check the finite sieve identities, not an empirical test of asymptotic (7). The Mertens/Markov argument is a paper deduction.

460968 greedy two-post-value tube controls at finite T=17,47,74955 with positive selected gain,76685 exact support divisibility and label capacity checks;166978 flat controls,1023 with positive high gain. Greedy controls had no same-stratum twin pair, so additionally grouped actual nonreset visits with same positive adjusted D across arbitrary intervening events:1165 selected stratum controls,1178 repeats,147 twin-gap incidences. Example root M2593, p29,D58,q179/181,H5190/5250,w43/10,ordinary post deficits64/58,physical gain88 including last event. Both waits>6, both long by 4w>=p-1, and cofactors prime by direct factorization. This is a small finite stratum witness, not a dynamically cube-certified pair. Another M1811,p7,D98,q521/523,post98/104. The asymptotic support count in (11)-(13) uses T_k^k>O(Y), not the small diagnostic T values. All final assertions passed. No Lean executable/kernel verification. No new Fourier exponent, external novelty claim or finite-twins contradiction. Main and sibling branches not modified.
