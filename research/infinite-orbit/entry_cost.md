# Hypothetical infinite MIN worlds V: semiprime entry sieve and frozen unit-stratum continuations

2026-11-26 JST. Independent continuation of [73a0130](https://github.com/tara-sooo/A166944-Lean/commit/73a01303cbc6c0bc73fa053a1e4e3a6e3525f21a). Sources: [IV low relays](https://github.com/tara-sooo/A166944-Lean/blob/73a01303cbc6c0bc73fa053a1e4e3a6e3525f21a/research/infinite-orbit/low_relay.md), [III exact clock capacity](https://github.com/tara-sooo/A166944-Lean/blob/ae36ba7e6002e69244233f89fbd810c04a68bbea/research/infinite-orbit/phase_graph.md), direct [3793617 fixed-dimensional prime-line upper sieve](https://github.com/tara-sooo/A166944-Lean/blob/3793617fd82ac3fa0b68679a57529fce233b3660/research/2026-11-26-min-direct-deficit-chain-sieve-and-global-log-obstruction.md), [bc3b10b localized deficit sieve](https://github.com/tara-sooo/A166944-Lean/blob/bc3b10b88fe25e845935164e571bed5f650ace87/research/2026-11-26-min-direct-low-scale-localized-deficit-sieve.md), unified [f1f6e1c uniform core clock resource](https://github.com/tara-sooo/A166944-Lean/blob/f1f6e1cc8a57adfc3252c4e5ba13654e4a3bf73f/research/2026-11-26-min-unified-uniform-core-clock-resource.md). This is a paper deduction using the earlier analytic upper sieve, and finite exact clock computations, not a Lean kernel proof or novelty claim. No changes to sibling branches.

## 1. From the two-neighbor roughness constraint to a semiprime sieve

Fix lambda>1 and eta>0. Consider canonical odd roots M with H0=2M-2 in [X,lambda X]. A good event means an actual adaptive MIN event at H with p>=eta sqrt X and w>=p-2. It need not have safe endpoints, and its ancestry may use ANY labels. Restrict the preceding horizon gain E=H-H0 to 0<=E<=D, where 0<=D<=X. Thus H=O_lambda(X) and p<=sqrt(H+1). All constants below may depend on lambda,eta but not D.

By III's exact local wait upper bound, each prime factor of H-1 or H+1 is >=(p-1)/2: a smaller factor is eligible and would force the wait below p-2. For sufficiently large X a composite neighbor has exactly two prime factors with multiplicity, because three factors of that magnitude exceed H+1. In particular, for the selected side e=1-2s,
    H=pq+e, q prime, H+e=pq+2e,
    2M=pq+e-E+2.                                     (1)
Here p,q=Theta_(lambda,eta)(sqrt X), including q=p if it occurs. The other neighbor is rough (prime or semiprime). These are arithmetic consequences of selection, not a probabilistic assumption.

For a fixed even E, p, e, write q=2v+1. The possible v lie in an interval of length O_(lambda,eta)(sqrt X); pad it to a common N=ceil(C sqrt X), with C sufficiently large. The forms q=2v+1 and pq+2e=2pv+p+2e must avoid every prime below z=floor N^(1/12). The latter avoidance is necessary by roughness; q itself is a prime >z. For primes f>3 other than p the two linear forms have distinct roots modulo f, since their determinant is 4e. The leading coefficients are 2,2p; p>z eventually. The fixed-dimensional Selberg upper bound used in direct therefore counts O(N/log^2 N) possibilities for each p,e,E. It applies to rough values as well as primes, since the argument counts survivors of the excluded small-prime residue classes. Sum over O(sqrt X/log X) possible p, the two sides, and E to get
    # odd roots with a good event at gain E<=D
        << (D+1) X/log^3 X.                          (2)
This is an upper bound on source roots; the sum can overcount many events of the same root. It does not require the good event to be the first one.

### Prime-root refinement with averaged exceptional factors

For prime M add the form
    M=pv+(p+e-E+2)/2.
Its constant term is integral because p,e are odd and E even. It too avoids all f<=z. For f>3, f!=p, the three forms have distinct roots except possibly at primes dividing (e-E+2)(e+E-2). Both factors are odd and nonzero for every even E; the determinants between q and M, and between pq+2e and M, are exactly e-E+2 and p times e+E-2 respectively (sign irrelevant). Thus the third form never coincides identically with another. The dimension-three upper sieve with exceptional primes omitted gives
    << N J_3(|e-E+2|) J_3(|e+E-2|)/log^3 N,         (3)
where J_3(n)=prod_(f prime>3, f|n) (1-3/f)^(-1). The factor is the cost of omitting exceptional local restrictions, as in the earlier fixed-dimensional sieve (finite primes <=3 absorbed into the constant). No exceptional factor involving p is charged because p>z.

The average of the product over even 0<=E<=D is O(D+1), uniformly in D. Indeed J_3(n)^2 is a divisor sum over squarefree d with prime factors >3 of a multiplicative weight a_d>=0, a_f=(1-3/f)^(-2)-1=O(1/f). For any L>=1,
    sum_(1<=n<=L) J_3(n)^2
        <= L prod_(f>3)(1+a_f/f)=O(L),
since the product converges. Each |e+-E+constant| is a nonzero integer <=D+3, with at most two preimages. Cauchy-Schwarz bounds the summed product by O(D+1). This avoids a growing worst-case loglog loss. Sum (3) over p and sides to obtain
    # prime roots with a good event at gain E<=D
        << (D+1) X/log^4 X.                          (4)
Both (2) and (4) include all possible earlier medium or bad-high events. The input analytic result is the standard fixed-dimensional Selberg upper sieve as used by the cited direct paper; the finite tests below check exact factor identities and sample counts, not that asymptotic bound or its constants.

## 2. Entry gain, medium supply and tagged resource

For a set of Theta(X) distinct odd canonical roots, (2) shows the fraction entering the good-high class before displacement D=o(log^3 X) is o(1). For a set of Theta(X/log X) distinct prime canonical roots, (4) gives exactly the same conclusion. This is stronger than IV, which only gave O((M_R+1)X/(loglog X)^2) for arbitrary odd roots and did not provide a relative prime-source estimate.

For either dense source class choose D=floor(c log^3 X) with c>0 sufficiently small depending on the sieve constants and the lower bound on source density. Then at least a fixed positive fraction (e.g. one half) have NO good event starting at displacement E<D. Under finite twins, all sufficiently large canonical adaptive rays are infinite. Stop each such ray at its first plateau reaching H0+D. Every event of this prefix has pre-displacement <D, hence none is good. The total prefix gain G_pre>=D (overshoot O(sqrt X)), elapsed ticks W_pre>=(G_pre-6)/2 by canonical nonnegative deficit. This argument is conditional on the rays reaching that plateau. Actual finite twin stops in the audit are kept separate.

Fix R, let M_R be the exact max low-only gain from IV, and r_R the least odd prime >R. Split this prefix into low labels p<=R and all others, with bad gain B_bad from the latter. All outside labels are medium or bad high, since no good event starts before D. By IV,
    G_low <= M_R(1+B_bad/(r_R-1)).
Hence
    B_bad >= max(0,(D-M_R)/(1+M_R/(r_R-1))).          (5)
For fixed R this is Omega(log^3 X) for the positive fraction of sources. This includes the possibility of a single large bad jump supplying the cost. If every outside event has label <=Y, the bad-event count on these prefixes is at least B_bad/(Y-1); otherwise a larger label itself pays gain. For growing R the exact inequality remains valid with H+1>=R^2; the bound weakens with M_R, and no fixed constant Omega is asserted in that case.

Summed over the original source tags in a dense family of N roots, the prefixes have at least Omega(N log^3 X) actual elapsed time and bad gain at fixed R. This count is *tagged*: two paths sharing physical events still contribute once per source incidence. It can be carried into the unified exact-core accounting only according to whether those events are omitted or belong to an actual selected core; it is not automatically a lower bound on Mhat, and it is submacroscopic compared with NT for T polynomial in X. This is a new quantitative initial-entry supply obstruction, not a uniform bound on the length L_R of an arbitrary later mixed run.

## 3. Frozen clock at shallow entry, regardless of earlier labels

For any actual canonical prefix of gain E, the wait bound gives 0<=d<=6+5E. If a good event has p>max(9,d+1), IV's exact unit-stratum formula applies even if the prefix contained arbitrary medium/bad high events:
    H'=H+p-1,
    d'=2p+6s,
    n=(H'+2p+6s)/2.                                 (6)
For example all good events with E<=D=o(sqrt X) satisfy the hypothesis eventually. Thus after the first shallow good event the full physical state (H',n) is determined by H,p,s, irrespective of prior clock phase. There is no free phase choice for the later relay.

Moreover the map from (H,p,s) to (H',n) in (6) is injective. From d'=2n-H', d' mod4 is 2 if s=0 and 0 if s=1 (p odd), so recover s, p=(d'-6s)/2, and H=H'-(p-1). A unit-entry post state receiving canonical sources with E<=D therefore has multiplicity at most floor(D/4)+1 (H0=0 mod4 in [H-D,H]), and different first high triples cannot merge directly at this first post-state. This does not control later merges or arbitrary non-unit-stratum entrances.

For exact finite continuation without guessing t, enumerate actual H and selected p,s. Form n by (6), require n=0 mod2p on s=0 or n=p+2 mod2p on s=1, and reject smaller competing ties. Let d_q be the positive backward clock gap of every eligible q at n. An admissible start with 0<=d<p-1 and w>=p-2 exists iff the following integer interval is nonempty:
    max(p-2,ceil((3p-1+6s-(p-2))/2),n-(3H+3))
      <= w <=
    min(min_q d_q,floor((3p-1+6s)/2),n-H/2).
The selected p is among q, hence min<=2p. This is exactly the rearrangement d=3p-1+6s-2w plus III's earliest-clock test. Require p>9 separately. All choices of w in the interval give the same post-state, so test just one. Subsequent low relay and actual high events are deterministic. This removes the O(sqrt X) arrival enumeration per candidate of III/IV for the unit-entry class. A possible start here is still an arbitrary intermediate state in the envelope; not every candidate is reachable from a canonical root.

## 4. Finite diagnostics

Final source [21c0110](https://github.com/tara-sooo/A166944-Lean/blob/21c0110d57b33cc0b289e84d17ceaf3a3ed6c8d8/research/infinite-orbit/entry_cost_audit.mjs), blob66b7ed1eb6f3e5aee352ebd541a71075d97cf535, exact remote readback. Run node research/infinite-orbit/entry_cost_audit.mjs. Actual ECMAScript execution, not separate Node. Final assertions pass. The original write succeeded but its readback call had an undefined path variable; fetched and executed remote source, then added factor-form checks and independently verified final content exactly.

A. Canonical prefixes: H0=0 mod4 in [X,4X), X=4096,16384,65536,262144. First long event p in [ceil(sqrt X/2),floor sqrt X] observed before displacement 512, or actual stop/censor at 512. The lower/upper finite band is a subset of the paper's good class. No endpoint safety imposed for this scan.
261120 distinct roots in the four disjoint windows, 43081 of them prime. 3802520 actual events scanned; 32936 observed first band-long events, 29026 with p>max(9,d+1), every one unit stratum. 102161 actual neighbor-factor roughness checks; 32880 prime-cofactor certificates in cases satisfying the finite sufficient cube exclusion p*((p-1)/2)^2>H+1, 5499 prime-source three-form checks in that subset. Other finite cases not claimed prime cofactor by that test.
| X | odd roots | prime roots | first good E<8 (all / prime) | E<32 | E<128 | E<512 |
|---:|---:|---:|---:|---:|---:|---:|
|4096|3072|719|87 / 18|207 / 36|527 / 110|749 / 161|
|16384|12288|2484|283 / 62|670 / 138|1354 / 293|2277 / 490|
|65536|49152|8739|822 / 133|1976 / 347|4212 / 750|7727 / 1394|
|262144|196608|31139|2449 / 342|5749 / 893|11867 / 1865|22183 / 3472|
At largest X, among 31139 prime roots, 1509 stop before E=8 without good, 3815 before E=32, 8225 before E=128, 15688 before E=512; 11979 cross 512 without a good event. These stops are real finite twin centers, not counted as continuing rays. Do not infer the hypothetical finite-twin prefix resource from raw finite fractions. Representative actual prime root M=131101,H0=262200 reaches H=262680 at t=131400, p=347,w=460,E=480,d=120,d'=694.

B. Exact unit-entry mixed continuations in [X,16X), same fixed high band as previous checkpoints, high endpoints distance >12 from multiples of 210; intervening labels <=R (R=3,7,11). For R=11 the low labels need not avoid crossing the fixed 210 lattice, so no claim that every physical cut is bypass; only the high endpoints are restricted. 480152 factor/endpoint candidates, 6514 feasible unit-entry triples, each simulated for all three R. 133 independent literal gcd controls on representative maximal words (duplicates included). For comparison previous arbitrary-phase max high counts with R=7 at first three X were 3,4,3.
| X | unit entries | R=3 max span / high count | R=7 | R=11 |
|---:|---:|---:|---:|---:|
|4096|171|112 / 2|130 / 2|130 / 2|
|16384|511|204 / 2|216 / 2|234 / 2|
|65536|1456|432 / 2|460 / 2|460 / 2|
|262144|4376|930 / 2|960 / 3|960 / 3|
Max span and max count optimized separately. At largest X, R=7, exactly 77 of 4376 feasible entry triples continue to a second good high and only one to a third. No triple reaches four highs in any tested unit-entry window. Positive 3-high exact word from H=2434302,t=1217290, p=281,w=285:
    labels 281,3,5,3,263,3,5,3,7,5,3,7,317
    waits  285,5,7,5,363,3,9,3,2,8,2,13,553.
It satisfies unit entry, full MIN competition, and high endpoint safety. The initial state has d=278<p-1; its canonical ancestry was not established. In contrast the separate max-span word at this X has only two highs. This finite computation excludes longer words in the stated unit-entry class in these windows; it does not exclude arbitrary later mixed runs or four-high paths at larger X.

## 5. Remaining obstruction

The semiprime sieve adds a genuine log^3-scale early bad-resource requirement for dense ordinary or prime sources under finite twins; the frozen state removes most phase freedom at shallow entry and exact low relays can be composed thereafter. It does not force macroscopic bad supply, and the uniform arbitrary-state bound L_R=O(sqrt X) from IV is still open. Medium relay cost (5) applies to arbitrary pre-entry labels but not a uniform length bound on mixed runs. Next: study repeated unit-entry-like strata after large deficit recovery, source multiplicity under exact first-high maps and later merging, and quantify the medium/bad-high resources inside unified common cores rather than only near roots. No full all-constraint survivor, Lean verification, or final finite-twin contradiction.
