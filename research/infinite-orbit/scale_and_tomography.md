# Hypothetical infinite MIN worlds II: first-event tomography and a deep-bypass scale survivor

2026-11-26 JST. Continuation of [62db949](https://github.com/tara-sooo/A166944-Lean/commit/62db949cdd9aac4b71cf550b962e4211e20cd22c). Independent branch. Paper deductions and finite diagnostics, not Lean kernel verification or external novelty claim. Two different relaxations are analyzed: the joint residue world from I, and a new integer-scale scalar clock model. They are NOT one combined survivor.

## A. Recover the common root from bare event words

Let rho be ANY compatible assignment of residues at odd primes, with odd root parity. For each nonnegative even offset k use the uncut virtual MIN rule of I, with root R=rho+k, canonical initial state and initial gain zero. At relative tick j, the test for an eligible clock is
    p | h_j, h_j=2j+7 (j odd) or 2j+1 (j even),
    rho(p)+k+j+2=0 mod p (j odd),
    rho(p)+k+j=0 mod p (j even).
Suppose p is the first selected nonunit label at j. This event ALONE forces any actual integer base M realizing the same event word to satisfy
    M = -k-j-2*1_{j odd} mod p.                       (1)
The deduction also holds for adaptive MIN, regardless of the negative/excluded clock constraints; selected p must additionally be eligible. The assigned artificial composite factors from I are not used in (1).

### A1. Every prime is visible somewhere in the family

Fix any odd prime p. Choose an even offset k so the virtual root R satisfies 2R=1 mod p. At the initial horizon C=2R-2 the plus neighbor C+1 has factor p and the minus neighbor does not. Its parity-compatible clock arrives within 2p future ticks. For every other odd prime q<=4p+7 choose R mod q avoiding 2R=1 and 2R=3 mod q. Such a residue always exists, even for q=3 (at most two forbidden residues). These congruences on k are mutually compatible by CRT, including k=0 mod2, and have arbitrarily large nonnegative solutions.

Before the first p clock, all h_j have absolute value <=4p+7; every possible eligible q is among those constrained. No q other than p can divide either initial neighbor. Hence the first event is p, within 2p ticks. Thus every odd prime has a witness in the family, with a finite explicitly computable offset and event time. One can take k less than twice the product of odd primes <=4p+7; no polynomial-size witness bound is claimed.

Consequence: the map from the entire residue assignment to the ordered first-event words of ALL even-offset sources is injective. If a fixed standard odd M realizes these words for all k (either uncut or adaptive), (1) implies M=rho(p) mod p for every odd prime p. This proves a stronger nonrealizability result for model I than its explicit composite-certificate obstruction: even if we discard ALL designated composite-factor certificates, the full indexed ensemble of bare first-event words cannot be realized by any fixed standard M. Indeed rho(q_b)=-b/2 mod q_b, so a realizing M would imply q_b|2M+b for every b, impossible since q_b>b^2+3 for arbitrarily large positive b. This does not prove that a SINGLE label ray is nonrealizable. The common root and fixed offset labels are essential.

### A2. Exact finite lower bound from only the observed labels

For a finite set W of observed first events, define P=2 prod_{p observed} p, with distinct primes, and solve (1) with M odd. If incompatible, no realization exists. Otherwise every possible M belongs to a unique residue a mod P, 0<=a<P. For roots >=5 the smallest representative is
    m0=a+P max(0,ceil((5-a)/P)).
Any realization within a finite root interval [L,U] must belong to that same progression; intersecting it with the interval gives an exact count of candidates for POSITIVE event congruences. This is a necessary filter, not sufficient for actual MIN realization: earlier ticks and adaptive eligibility still need checking. If no candidate exists, this alone excludes a simultaneous realization.

There is a useful simpler lower bound in model I: every observed prime with rho(p)=1 forces p|M-1. If P1 is their product, M>=5 implies M>=P1+1, regardless of the designated factors or missing quiet constraints. A witness with rho(p)!=1 also excludes M=1 if allowed.

### A3. Finite actual audit and bounded-scale obstruction

Reproduce with node research/infinite-orbit/scale_tomography_audit.mjs. The exact ECMAScript function executed, not a separate Node process. Use the deterministic rho of I, even offsets 0..K, first-event observation up to 2048 relative ticks. For each distinct observed prime retain a witness; solve positive CRT with BigInt. Independently enforce all potential clock residues of these witness prefixes and check the literal parity gcd in one common arbitrarily large integer lift. 30 explicit CRT tomography controls p<=127 and 118699 literal tick comparisons across selected witness sets pass. Counts overlap across nested K. Roots without an observed first event are not declared terminal and impose no positive constraint.

| K | sources | observed nonunit | distinct labels | largest p | digits of P | candidates M in [K,2K] |
|---:|---:|---:|---:|---:|---:|---:|
|64|33|33|9|61|12|0|
|256|129|128|16|227|23|0|
|1024|513|510|35|1789|66|0|
|4096|2049|2031|70|3169|159|0|
|16384|8193|8085|154|3677|399|0|

At K=64 the 9 witnesses (k,j,p,r) are
    (2,1,3,1), (6,2,5,2), (60,16,11,1),
    (42,3,13,5), (0,5,17,10), (48,25,19,1),
    (18,18,37,1), (24,67,47,1), (30,30,61,1).
The minimal odd M>=5 satisfying these positive congruences is 20086482967. P1=66511533 already gives a large lower bound without the nonunit residue witnesses. For K=16384 the minimal CRT representative has 398 decimal digits. No designated composite factors were included in the positive CRT filter. Arbitrarily large actual adaptive lifts of the first-event witnesses are possible, as the independent full-residue lift confirms.

This is a concrete fixed-window failure of the residue ensemble. No conclusion that m0(K)/K diverges for all K is inferred from the finite table or the all-offset injectivity theorem. In particular the offset witnessing a prime via CRT may be enormously larger than that prime.

## B. Independent absolute-scale scalar survivor

Use the latest direct note [2a47be1, grouped cut sieve and all-label corridors](https://github.com/tara-sooo/A166944-Lean/blob/2a47be177db12d7fdcdc99daf9dfe7be0403da34/research/2026-11-26-min-direct-grouped-cut-sieve-and-all-label-corridors.md), and [3793617, deficit-chain sieve](https://github.com/tara-sooo/A166944-Lean/blob/3793617fd82ac3fa0b68679a57529fce233b3660/research/2026-11-26-min-direct-deficit-chain-sieve-and-global-log-obstruction.md). Here construct an infinite scalar clock trajectory with standard integer horizons, prime labels at square-root scale, nonnegative deficit, exact selected parity clock, and deep bypass cuts. It deliberately lacks neighbor divisibility, actual MIN competition and true ancestry. It is not asserted to satisfy any theorem whose actual-MIN hypotheses fail.

### B1. Choose labels and keep every endpoint away from the pinned lattice

Use X_i=16^i X0. In each block let S_i,R_i,K_i=2P_{S_i}, V_i=4 floor(S_i^2/4), ell_i and kappa_i be the cut parameters of 2a47be1. In this section use V_i only for corridor radius; denote ordinary total variation by TV_i. For large X_i the source's prime asymptotics give S_i~R_i/loglog R_i, R_i~(log X_i)/2, log K_i~S_i, hence K_i/(V_i log X_i)->infinity and V_i=o(sqrt X_i). The same bounds hold for i+1 when X_{i+1}=16X_i. A safe endpoint is at distance >V_i from every multiple of K_i. Surviving cuts are a subset of this lattice. Choose the initial even H0 divisible by 4 and within O(V_0+1) above X0 that is safe; t0=(H0+6)/2 gives canonical odd root M=(H0+2)/2. For every step in block i choose a prime
    sqrt(X_i)/2 <= p <= sqrt(X_i),
such that H+p-1 is safe for both lattices i and i+1. Also exclude the previous selected label if desired.

Existence of a choice for EVERY H: a forbidden band of endpoint residues mod K has length at most 2V+1. The number of integer p candidates in an interval of length O(sqrt X) hitting it is at most (2V+1)(O(sqrt X/K)+2). For either lattice this is o(sqrt X/log X), since V is polylogarithmic, K/(V log X)->infinity. The prime number theorem used in the source provides asymptotically positive order sqrt X/log X primes in the band. Thus even after discarding both forbidden subsets and finitely many labels, there is a remaining prime. This does NOT require primes in progressions with growing modulus. One may optionally exclude all prime factors of H-1 and H+1 in the band (O(1) of them since H=O(X)); this makes the failure of actual divisibility explicit. The finite audit below did not apply this extra exclusion.

Update H'=H+p-1, change block after first H'>=X_(i+1). The dual safety condition on the previous step ensures the new block starts safe. Gains are positive, sqrt-scale, and the crossing overshoot is O(sqrt X_i); the entire process has infinitely many blocks. Total gain G_i=15X_i+O(sqrt X_i), event count n_i=Theta(sqrt X_i). Adaptive magnitude inequality p^2<=H+1 holds on every event.

### B2. Clock and deficit with large variation

For current t, the two possible parity clocks for label p have residues n=0 or n=p+2 mod 2p (even n divisible by p, odd n with p|n-2). Let w be the later of their next positive waits. Their circular distances are p-2 and p+2, so p-2<=w<=2p. Set t'=t+w, d'=2t'-H'. The selected side's time congruence holds exactly; no claim that the same side's neighbor is divisible.

Writing g=p-1 gives
    d'-d=2w-g >= p-3=g-2,
    d'-d<=3p+1<=5g.
In particular d increases and d>=6, every wait has the correct scalar upper bound. Therefore TV_i=d_end-d_start is between G_i-2n_i and 5G_i, i.e. Theta(X_i). Starting from fixed d0=6 gives d=Theta(H) along the tail. For any selected population in any band the direct global logarithmic lower bound on U+TV is satisfied with wide margin, since TV alone is Theta(X_i). The high-band local chain theorem with its sublinear adjusted-deficit cap is not activated: these scalar deficits are linear and the actual factor/ancestry conditions are absent. Thus a large-variation world is not excluded by those aggregate lower bounds.

### B3. Every surviving cut is deep bypass

In every block both endpoints of each jump are safe for the current lattice. No exact anchor, launch, or landing is possible: for each surviving cut J strictly inside a jump, J-H>V_i and H'-J>V_i. All cuts are deep bypass even in the larger entire pinned lattice. The normalized surviving-cut mass is G_i+o(X_i) by the direct source's uniform cut counting on an interval, which is purely arithmetic and does not depend on the trajectory being actual MIN. Endpoint corridor demand is zero. Also the union of eroded intervals retains all these cuts. Applying source (4) to the disjoint erosion intervals gives a smoothing error O(ell_i n_i)+o(X_i)=o(X_i), since ell_i<=X_i^(2/11)+O(1). The total erosion loss O(V_i n_i)=o(X_i). Thus bypass capacity at the macroscopic scale is consistent with the available gain, even when exact-anchor and endpoint mass vanish. Source (8) uses both direct and smoothing bounds; our actual lattice cuts obey both, so its minimum envelope holds as well. No local fast-wait corridor requirement is triggered at a safe endpoint.

This is a genuine infinite construction in the explicitly defined relaxed scalar clock domain. It combines absolute magnitude, prime labels, selected time congruence, unbounded gain and labels, linear variation, adaptive magnitude, and cut geometry. It is NOT an actual trajectory, and the inferred compatibility is only for the listed scalar/cut constraints; do not use it as a counterexample to actual MIN results. In particular actual horizon divisibility, selected post-deficit stratum, competition, and dense-source transport remain outside the model. The deep-bypass and macro upward supply alternatives can coexist at the scalar level; eliminating one by assuming the other absent would miss this surviving regime.

### B4. Finite diagnostics

Reproduce with node research/infinite-orbit/coarse_scale_audit.mjs (final [6d686a3](https://github.com/tara-sooo/A166944-Lean/commit/6d686a3e58d7932f431a0ccb64bd1c99a1338415)). Actual ECMAScript execution. Four independent windows, fixed diagnostic S=7, K=210, V=12, not the asymptotic parameter sequence. Greedy prime selection, forbidding immediate same label. This is not an audit of the PNT asymptotics or a complete joined infinite computation. Counts:
| X | events | total gain | total variation | pinned cuts (all bypass) | failed neighbor divisibility | failed selected time clock |
|---:|---:|---:|---:|---:|---:|---:|
|65536|7022|983066|2021836|4681|6978|0|
|262144|14980|3932250|8123614|18725|14924|0|
|1048576|29960|15728968|31195152|74900|29909|0|
|4194304|59919|62914782|125991142|299595|59867|0|
The failed neighbor divisibility counts are intentional diagnostics of the missing arithmetic condition, not failures of the relaxed model. All asserted scalar and selected clock checks pass. The original preliminary audit used w=p; replaced by the later-clock construction and reran final exact source.

## C. Next obstruction: couple the two domains

I and A show that an infinite consistent residue world need not permit standard bounded-scale dense-root realizations even for bare first-event words. B shows that absolute-scale scalar budget conditions and selected time congruences, even with the newest deep-bypass constraints, admit a different infinite survivor. Neither model is the intersection.

Next: impose actual horizon divisibility at B's safe endpoints and exact first-hit competition, preserving the post-deficit stratum and actual root history. A useful finite relaxation is a directed DAG on integer states (H,t), with eligible p from actual H+-1 and both clock and cutoff tests, then enforce earliest choice and record physical shared states. The bare word CRT filter in A should be applied on overlapping bounded source windows before any dense-source mass is assigned. A necessary quantitative goal is either a bound on how many genuine safe deep-bypass events can supply gain at each scale, or a realizable explicit sequence with those conditions. Do not transfer the entire residue world using unbounded lifts, nor assume the unified macro missing hypothesis. No full theorem inventory, no complete all-constraint survivor or finite-twins contradiction, no Lean execution.
