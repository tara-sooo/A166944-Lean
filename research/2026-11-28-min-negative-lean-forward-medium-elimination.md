# Negative MIN: forward three-high-event elimination of the medium expense

## Scope and status

Continuation of the independent Lean live-survival branch, not a claim of twin-prime infinitude. Keep the original negative MIN rule, canonical roots, physical cap, observation window and weighted expenses of the paper criterion in 5a221805964d0d023f1577e066e67ec984d0aa66 and the exact net maximizer in 910f12bd8b5dfaf1806ec67a5a1c00a39e55bd4d. Finite algebra and orbit lemmas below are kernel checked; the uniform asymptotic counting argument is a paper-level derivation, not yet a Lean theorem or independently reviewed result.

Verified Lean core: 70180a453cb99bd6cfec0e72f100f052cff2d3c0 (blob 8352acfee5f9ea679773b60b9723a9bd83e3d898), CI run 46026237863, Lean v4.33.1, 313 theorem declarations (previous 238). No sorry/admit/axiom declarations; selected theorem dependencies are propext, Classical.choice, Quot.sound only. The Mathlib weighted criterion adapter has not been checked.

## 1. First-use, imbalance and record perturbation

In the notation of NegativeMINCore.lean let K_A count all narrow events z<p<Y0 on the actual prefix, and Q_A sum 2q(x) at medium events Y0<=p<Y1 with p^3<=(2q(x))^5. The prefix includes pre-observation events and the last completed tick even if it kills the selected root. Each positive first charge of a label occurs at most once. Filtering by positive charge before the unused-label recursion is essential when roughness or balance can vary between successive uses of the same label.

The kernel-checked residualExpense_partition and removedExpense_bound decompose the original weighted expense into repeated positive narrow and balanced medium charges plus removed expense e_A. For U>0, balanced medium means p<Uq(x); imbalance means Uq(x)<=p. Using q(x)<=p and the jump gain p-1 gives, for prefix age k,

    U e_A(k) <= U(wN Y0 + 2 wQ Y1^2) + 3 wQ(2k+6).

The first-use bound is deliberately coarse; no prime number asymptotic is needed. The removed and residual prefix expense sequences are nondecreasing. For any two integer sequences f,g with g's increments >= f's, the record-profit increments of g dominate f pointwise, and

    sum_{i<k} (profit_g(i)-profit_f(i))
       <= (g(k)-f(k))-(g(0)-f(0)).

This is checked by recordProfit_mono_increment and recordProfit_sum_perturb. In particular the residual record-profit profile is a valid pointwise upper approximation to the original one; the total change is controlled by removed expense. This does not assert that residual history-dependent expense is a state-dependent increment or that the original contact-priority theorem applies to it.

## 2. Forward finite ledger (Lean checked)

Fix any actual prefix, with all events of label >=Y0 listed in chronological order. Call such events high for this section; medium charged events are a subset. For every medium charge at p, examine the next two high events r,s **within the same prefix**. A clean triple means that both intervening gaps contain only labels <=z (and idle ticks), and r,s<U Y1. Put F_A equal to the sum of the *first* medium charges of clean triples. There are three alternatives:

* No two successors: at most the last two high events, total charge <=4Y1.
* A narrow event in either gap: each narrow event belongs to one gap, shared by at most two starts, so the total charge <=4Y1 K_A.
* A successor >=U Y1: its gain pays for at most two starts, so the total charge <=6G_A/U, with G_A the actual prefix gain.

The exact theorem medium_forward_reduction states, without division or a positivity requirement on U,

    U Q_A <= U F_A + 4 U Y1(1+K_A) + 6 G_A.

Here highLedger records the ordered high states and the exact narrow count in each following gap; sumTriples traverses overlapping consecutive triples, lastTwoSum handles the tail. medium_forward_total sums the ledger and uses G_A<=3T+6 for every canonical root. With N roots, K=sum K_A, Q=sum Q_A, F=sum F_A,

    U Q <= U F + 4 U Y1(N+K) + 6 N(3T+6).                 (1)

No probability, independence, or cap assumption is needed for (1).

## 3. Clean triple bound (paper-level analytic argument)

Let L=log R, T=floor(ceil(sqrt(2R+1)) exp(-L^0.5)), M=floor L^2.1, z=max(7,floor sqrt(log L)), Y0=ceil exp(L^0.45), Y1=ceil exp(L^0.85), d=0.6, U=ceil L^3. The exact rounded parameters are interchangeable in the asymptotic estimates here. Use the original synchronized windows of width 6 floor(T/6). Canonical roots A are multiples of 6 in [R,2R], birth clock 3-A/2. A FullCapped policy caps each pre-tick physical fiber (window, center, clock) by M, including pre-observation. Its actual selected prefixes remain in [R-O(T),2R], age <=3T/2, gain <=3T+6. A given center is accessible from O(1) windows, and its accessible firing clocks occupy an interval of length O(T), since the initial root is within 3T+6 of it. The number of canonical roots N is asymptotic to R/6.

Let B=Q_z=2 product_{3<=ell<=z, ell prime} ell. Then B=L^o(1). The previously checked small-label wall bound implies that each of the two intervening relay gains E1,E2 is <B. For a clean triple with labels p,r,s and sources x,y,v,

    Y0<=p<Y1,  Y0<=r,s<U Y1,
    y=x-(p-1+E1), v=y-(r-1+E2).

The first source is rough: q(x)>=p^d/2. Each source is congruent to its sign (+1 or -1) modulo its label. Actual adjacent repetition requires relay gain >=p-1 (for p>=5), so p!=r and r!=s once B<Y0-1. Endpoint repetition s=p remains possible; actual_repeat_third_middle gives r>=p-E1-E2>=p/2. It is not permissible to assume three distinct labels.

For each fixed p,r,s, signs and E1,E2, the spatial congruences impose at most one class modulo J, the product of distinct labels (prs or pr). Here J=R^o(1), so even without sieving the spatial count is O(R/J). Clock pins use the firing clock (pre-tick clock +1): for sign -1 it is 0 mod 2p, for sign +1 it is p+2 mod 2p, and analogously for later labels. At specified positive gaps h1,h2, there is at most one class of first firing clocks mod 2J, hence O(T/J) choices at each spatial key. This uses J=o(T); compatibility may make the count zero.

The exact actual_two_clock_gap lemma states that between actual firings the time difference is at most 3E+2q(next source). It follows by decomposing into completed intermediate waits <=3 times their gain and the final wait <=2q(next). Its qmin premise is justified by leastOddFactor_sound and qmin_spatial, not a heuristic about the least divisor.

At each candidate first source and clock, the number of roots contributing the first charge is O(M) across the O(1) accessible windows. This is the physical cap at the first firing, not a bound on the number of histories visiting a later state. We count only completed first charges with two actual successors in their prefix. Overcounting possible successors in a CRT enumeration is harmless, since each actual contribution is included. Its weight is <=2p.

### 3a. Second source is nonrough

If q(y)<r^d/2, ignore the third event. For fixed p,r, signs and E1, there are O(R/(pr)) spatial candidates and O(B+r^d) possible positive clock gaps. Each gap gives O(T/(pr)) first clocks. The weighted first-charge count for each spatial key is O(M T (B+r^d)/r), hence O(M T Y0^(d-1)), since B<=Y0^d eventually. Summing over the spatial keys, labels and gaps gives, after dividing by NT,

    O(M (B+1) (log L)^2 Y0^(d-1)).

We used only the elementary prime harmonic bound sum_{Y0<=p<U Y1} 1/p = O(log L), and q<=label. This case does not require roughness of the third source.

### 3b. Third source is nonrough, second rough

For distinct labels, the two gaps range over O(B+r)=O(r) and O(B+s^d)=O(s^d) possibilities. With J=prs the weighted first-charge count per spatial key is O(M T s^(d-1)). The summed normalized contribution is

    O(M (B+1)^2 (log L)^3 Y0^(d-1)).

For s=p, the repeated label pins the sum of the two gaps to a specified residue modulo 2p. At fixed h2 there are O(1+r/p)=O(r/p) possibilities for h1, since r>=p/2. There are O(p^d) choices for h2. With J=pr, the weighted count per spatial key is O(M T p^(d-1)). Sum over just the two distinct labels; the same displayed bound suffices. Ignoring the repeated-label clock relation would lose an essential power of p.

### 3c. All three sources rough

In the remaining case all six integers x-1,x+1,y-1,y+1,v-1,v+1 are free of prime factors <Y0^d/2. On the CRT progression write x=x0+Jt, and set D1=p-1+E1, D2=r-1+E2. The six shifts are -1,+1,D1-1,D1+1,D1+D2-1,D1+D2+1 (with an immaterial change of sign for the first two). They are distinct because D1,D2>2. Let H be J times the product of all nonzero pairwise differences of the six shifts. Then log |H|=O(L). For each prime ell>=7 not dividing H, six distinct residues of t modulo ell are forbidden.

Here is the explicit upper-bound sieve input. Set Z=Y0^0.01. For squarefree integers m supported on the allowed primes, let rho(m)=6^omega(m), g(m)=rho(m)/m and h(m)=product_{ell|m} 6/(ell-6). Apply the Selberg quadratic majorant (sum_{m<=Z, m|bad(t)} lambda_m)^2, with lambda_1=1 and other weights supported on these squarefree m. The main quadratic form is minimized at 1/G(Z), G(Z)=sum_{m<=Z} h(m). This follows by diagonalizing g(lcm(m,n))=g(m)g(n) sum_{a|gcd(m,n)} 1/h(a) and applying Cauchy-Schwarz to the transformed variables; the inverse gives weights
lambda_m=mu(m) product_{ell|m}(1-g(ell))^-1 G_m(Z/m)/G(Z),
where G_m restricts the sum to integers coprime to m. Consequently |lambda_m|<=product_{ell|m} ell/(ell-6)<=m. The residue count error per pair is O(rho(lcm(m,n)))<=mn, and the weighted summed error is O(Z^6).

For the denominator, consider the Euler product restricted to allowed primes ell<=Z^c for a sufficiently small absolute c>0. The product measure selecting ell with probability 6/ell has mean log of the resulting squarefree integer <=6 sum_{ell<=Z^c}(log ell)/ell = O(c log Z). Choose c so the mean is <=(log Z)/2. At least half the product weight lies on integers <=Z, by Markov. Omitting the primes dividing H loses at most O((log L)^6) in the Euler product: for ell<=L use Mertens, and for ell>L use sum_{ell|H,ell>L} 1/ell <=log |H|/(L log L)=O(1/log L). Finite primes including 2,3,5 can be omitted. Thus

    G(Z) >> (log Y0)^6/(log L)^6.

The standard elementary prime harmonic estimates and Mertens used here are analytic inputs, not kernel-checked facts in this branch. The progression length X=O(R/J) has scale R^{1-o(1)}, and Z^6=R^o(1) is absorbed by the main bound. The spatial count is

    O((R/J) (log L)^6/(log Y0)^6).

For each surviving spatial key, now ignore the later clock constraints: O(T/p) first firing clocks and charge <=2p give O(MT) weighted mass per key. Sum over two relay gains, signs, and at most three distinct prime labels, taking s=p separately with the pr modulus. After normalization the bound is

    F_rough/(NT) << M(B+1)^2 (log L)^9/(log Y0)^6
                 = L^(-0.6+o(1)).

Both nonrough contributions are smaller than any fixed negative power of L. All estimates are uniform in the FullCapped policy. In particular this proof applies to repeated as well as first medium charges and needs no independence of the different root trajectories.

## 4. Consequence for the ORIGINAL weighted criterion

Write C_N=a_R K/N, C_Q=Q/(NT), with a_R=exp(-L^0.6)/(k_relay+1) and k_relay=Theta(sqrt(log L)) as in the earlier paper. Divide (1) by UNT. The result of section 3 yields the uniform paper-level estimate

    C_Q <= eps_R C_N + e_R,
    eps_R = 4Y1/(T a_R),
    e_R = O(Y1/T + U^-1 + L^(-0.6+o(1))).

In particular eps_R is smaller than every negative power of L and e_R=o(L^-1/4). Therefore on the original slabs, the original CheapSurvival condition is equivalent to requiring the same lifetime lower bound eta >> L^-1/4 and C_N=o(L^-1/4) alone. Indeed original cost is nonnegative, and conversely the displayed bound makes C_Q=o(L^-1/4). This is a reduction of the cost estimate, not a change in the target. No finite-twins assumption is used.

The original paper-level WeightedEstimate is eta <= B0 M (#twins)/N + C(C_N+C_Q) + o(L^-1/4), with C constant. Combining it with the new estimate gives the same inequality with C(1+eps_R) C_N and adjusted o(L^-1/4) error. The previous quantitative twin count >> R/L^2.35 follows if cheap survival is established on unbounded slabs.

There is also an exact finite comparison of the maximizers from the preceding checkpoint. Let wN,wQ be original integer prices, D the integer observation reward per tick, V_orig the maximum of policyNet for weightedInc, and V_boost the maximum for boostedNarrow = (wN+4wQY1)*narrowInc. For d_boost an exact maximizing policy for boostedNarrow, the kernel-checked optimalNet_boostedNarrow_comparison states

    U V_boost <= U V_orig
      + wQ ( U F(d_boost) + 4 U Y1 N + 6 N(3T+6) ).

This holds with the original definition of FullCapped; the cap of d_boost is verified by optimalNetDeath_fullCapped. No claim that the two maximizers coincide. At the original scales take lambda=log L, D=ceil L^2, wN=ceil(D lambda T a_R), wQ=ceil(D lambda). The integer rounding errors are o(L^-1/4) after normalization by DNT, using K<=O(NT) and Q<=O(NT) by the gain ledger, and D large enough; the boosted price rounding is also harmless since Y1/T is subexponentially small. Section 3 bounds the normalized comparison error by O(lambda e_R)=o(L^-1/4). Hence a positive lower bound of size c L^-1/4 for V_boost/(DNT) on arbitrarily large slabs would transfer to V_orig and contradict a finite twin count by the original weighted upper estimate.

The exact optimum of the boosted narrow-only objective already has the previously checked optimalNetDeath_formula using per-root records and capped threshold sums. Its increment cost is the constant price only at z<p<Y0. First use of such labels costs at most wN*Y0 per root (with the corresponding boosted price if used), negligible at these scales. It remains to establish a genuine lower bound on this optimum, or equivalently for the separate CheapSurvival route to exhibit a policy with sufficient lifetime and small repeated narrow-event cost. There is no bound here on all narrow repetitions: total gain alone only bounds their number by O(T/z), far too large compared with the required roughly exp(L^0.6) budget. Thus this step is not obtained by repeating the first-use argument.

## 5. Reproducible finite audit

research/lean/negative_min_forward_three_high_audit.mjs at 9783d83b2c362f98d47b3455553324aebf97cdc5 (blob a0997a787169543901276df9e5d04248842cda1c); remote readback and reexecution matched. R=12000,48000,192000; 42003 canonical roots, 775263 actual events, 168012 selected prefixes for caps M=1,4,16,64; 382155 literal gcd-clock comparisons at R=12000. Total 3734004 counted checks. Forward clean triples 200086 across caps; endpoint repeats 15965. Checks include exact expense partition, finite inequality (1) per prefix, actual relay time, clock congruences, six-root exclusions, and repeated endpoint restrictions. Finite parameters z=5,Y0=11,Y1=floor(T/2),U=4,B=30. These are deliberately small test scales, not the growing asymptotic parameters; adjacent-repeat impossibility is tested with E<Y0-1, and the stronger endpoint ratio only where the relay sum is small enough. At R=192000,M=16 the original normalized medium charge is 0.61320986945, clean charge 0.22575272345. These values neither establish nor contradict the asymptotic result.

## 6. Open obligations

* Independent mathematical review and Lean formalization of the CRT and dimension-six sieve counting argument, the original WeightedEstimate, and the asymptotic normalization/adapter.
* Prove a growing-scale positive lower bound on the exact narrow-only net optimum, not just finite positive computations. In particular control repeated labels in the narrow band relative to cumulative survival under physical caps.
* No unconditional twin-prime infinitude or quantitative twin count has been established in Lean. The original target and Issue #10 stay open.

No new Mathlib dependency download or full project build was used. CI failures during proof elaboration were corrected; final checked source is the pinned commit above.
