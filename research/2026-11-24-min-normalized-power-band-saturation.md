# Normalized first saturation across power-size prime bands, and the small-label floor

2026-11-24 JST. Continues 6f843505423e8efe3bcc1c645b17b34daaddb9df on the SAME research/min-cycle-forest-2026-11-24 branch. New paper estimates using the standard two-linear-form upper-bound sieve, and exact finite audits. Not Lean-checked. No completed concentration bound or proof of twin-prime infinitude.

## 1. Setting and what is being improved

Keep canonical MIN, X dyadic divisible by four, N=X/2 odd original M in [X,2X), B=ceil(sqrt(7X)), original clocks and cutoffs, LOW7 L=210. A selected high key is (p,C) for p>7. All original tags preserved up to first absorption. If a preceding high key (q,D) feeds a proposed current high key (p,C), the previous note gives
    C=D+q-1+g, 0<=g<L even,
    2kq=(2k'+1)p+e, |e|<=7L+4r(C)+7,
    h_prev=b+2kq, h_now=b'+2k'p,
where h_now is the hypothetical post-height of the proposed event, even when stopped before execution. k,k'>=0, b,b' in {0,6}; e is odd. For p>7L+4r(C)+7 the previous high reset case k=0 is impossible; for p>6+6L+4r(C)+1 initial high arrivals are impossible. For q=p>L+3 the consecutive high-key horizon congruences are inconsistent. We retain the WHOLE executed parent mass m(q,D), not just its current subset.

The previous normalized-parent theorem considered p>=B/log^alpha B. Here we obtain a broader deletion for p>=B^theta with any fixed 0<theta<1, relative height h_now/p small and comparable previous label; we then show that at normalized-cap stops the smaller previous labels cannot supply significant mass. The argument uses primality of BOTH labels in a small-coefficient linear equation.

## 2. Comparable-parent transfer theorem on a full power band

Let alpha,beta,gamma,delta>0 be fixed with
    alpha+2 beta+gamma+delta<1.
Put F=log^alpha B, H=log^beta B, z=ceil(log^gamma B), W=log^delta B.
Consider ALL tag incidences of consecutive high keys satisfying
    p>=B^theta, r(C)<=z, h_now<=p H,
    q>=p/F, m(q,D)<=q W.
No restriction on the earlier depth or on the current mass. The current proposed event may reset, stop, or execute. For sufficiently large B there is a previous high event and it is nonreset, by section1 (and the stated q is genuine). Also q!=p. Put a=2k'+1, d=2k. Then
    a p-d q=-e,
    1<=a<=1+H, 2<=d<=O(F(H+1)), |e|=O_L(1+z).
The bound on d uses q>=p/F and ap+e=dq; the previous height need not be assumed small. Also q<=O(p(H+1)), and both p,q>=B^(theta/2) for sufficiently large B. For a fixed (a,d,e), we claim
    sum_{p,q prime in the stated ranges, ap-dq=-e} 1/p
        = O_theta((log log B)^2/log B).
Proof: if gcd(a,d) does not divide e, there are no solutions. Otherwise divide through by that gcd to get coprime positive coefficients a0,d0 and nonzero e0. All integer solutions take the form p=p0+d0 j, q=q0+a0 j. Consider each dyadic band P<=p<2P, P>=B^theta/2. The interval of j can be embedded in one of length O(P), comparable to P (actual length can be shorter). For each odd prime ell not dividing a0 d0 e0, both affine forms have invertible slope and two distinct roots mod ell, by the nonzero determinant. Omit primes dividing 2ade. This exceptional product divides a nonzero integer of polylogarithmic size in B. Its reciprocal sieve factor is O((log log B)^2): split exceptional primes at log B and use Mertens for the smaller ones, with bounded reciprocal sum for larger ones, as in the four-form transport note. Take sieve cutoff B^c with a sufficiently small fixed c depending on theta and level B^(theta/4); both actual primes exceed the cutoff. The standard dimension-two upper-bound sieve gives O_theta(P (log log B)^2/log^2 B) solutions, uniformly in the coefficients and interval positions. Indeed the squarefree residue errors O(2^omega(l)) summed to the level are O(B^(theta/4) log B), negligible against P/log^2 B. This remains an upper bound for a short interval embedded in length P. Divide by P and sum over O(log B) dyadic bands. This proves the weighted claim. There is no assertion of a lower-bound prime-pair theorem.

For fixed distinct labels q,p and the finite g/sign choices, q|D+/-1 and p|D+q-1+g+/-1 determine a CRT progression of even D of count O(X/(pq)), since pq<=B^2=O(X). The number of tags for each such pair of projected keys is <=m(q,D)<=qW, even if different clocks/low suffixes occur; each tag can use the same predecessor key only once. Thus for each (a,d,e) the tag incidence sum is at most O_L(X W) times the weighted prime-pair sum. There are O_L(F H^2 (1+z)) coefficient/offset triples. Hence
    I_comp <= O_(theta,L)(X (log log B)^2
                         log^(alpha+2beta+gamma+delta-1) B)
           = o(X).
With all four exponents 1/8 this is O(X (log log B)^2/log^(3/8) B).
The conclusion bounds all qualifying source incidences (thus also distinct roots) at arbitrary depth, not just candidate positions or a first-mark population. Compared with the preceding top-band theorem it covers a much broader CURRENT prime range but requires q>=p/F and h_now<=pH. These restrictions must not be dropped.

## 3. Pointwise small-donor bound at first normalized saturation

Use the variable cap tau_p=ceil(p W). Execute a proposed high key iff its mass is below its cap; otherwise absorb all its tags before execution. All earlier executed high keys obey m(q,D)<=qW. At a current key p>=B^theta, consider its distinct preceding high keys with q<p/F. For each fixed even g<L, each q divides C-g or C-g+2, and determines D. In each of these integers (O(X) and positive), there are O_theta(1) distinct prime factors >=B^(theta/2) and O(log B) factors in total. Therefore
    sum_{possible (q,D), q<p/F} q
        <= O_(theta,L)(p/F+B^(theta/2) log B).
The smaller-parent incoming mass is at most W times this quantity. Any initial arrivals contribute at most A=floor(L/4)+1=O_L(1) roots, since they must start within <L of C. In particular at a STOP of mass m>=pW, the small-parent fraction plus initial-root fraction is bounded by
    O_(theta,L)(1/F+B^(-theta/2) log B+1/(B^theta W))=o(1),
uniformly over all such keys. Summing over disjoint stopped populations shows that the total number of stopped tags of this kind is o(X). This is a deterministic source-mass estimate; it does not require low height or small r. It does NOT assert that small-parent arrivals along all intermediate unabsorbed keys are o(X).

Combining with section2 gives the following genuine extension of the prior normalized-stop deletion:
    #stopped tags at p>=B^theta, r(C)<=z, h_now<=pH = o(X).
Indeed the small-parent/initial tags at these stops are a subset of the o(X) bound, and comparable-parent tags are counted by I_comp. Other tags in the SAME stopped group may have high hypothetical post-height; the conclusion is tag-wise. No assumption that all group arrival clocks agree is used. The remaining large-p stops have r>z or h_now>pH (up to o(X) tags).

## 4. Hybrid cap with a floor to avoid premature small-label stops

The normalized cap can stop a large mass at a small p merely because the label decreases. For a tag at a first normalized stop, if its current whole group mass m is <= its own preceding whole mass m0, then
    pW <= m <= m0 < qW,
so q>p. If there is exactly one incoming nonroot class and no initial tag, m<=m0 automatically. The crossing is not evidence of any mass growth. This distinction is exact even if the projected group split along the way. With the hybrid cap below, the same inference q>p follows by monotonicity of the cap.

Fix 0<eta<theta<1. Use
    tau_p=ceil(W max(B^eta,p))
at every high key (round B^eta up if desired). The executed prefix cost is still o(X^2). The previous arithmetic estimates S_p=O(X/log^2 p), S_key=O(XB/log^3 B) and LOW block cost give
    R_pre = O_L(X + W X B^2/log^3 B
                  + W B^eta X B/log^3 B
                  + W X L [pi(B)+B^eta log log B])
          = o(X^2)
for the chosen small delta. Here the q term in the LOW penalty is summed using #keys for q=O(X/q); the floor term via harmonic prime sum. For any unstopped non-twin original source the previous Omega(X) prefix-cost lower bound applies. Thus in a no-twin window N-o(X) roots must still stop.

At p>=B^theta, q>=p/F eventually implies q>B^eta, so every executed comparable parent obeys m(q,D)<=qW, and section2 applies unchanged. For small parents use the same factor count as in section3 to obtain
    sum_{possible (q,D),q<p/F} max(q,B^eta)
       = O_(theta,L)(p/F + (B^(theta/2)+B^eta) log B).
This divided by p tends uniformly to zero since eta<theta. The cap at the current p is still pW up to rounding. Therefore the same o(X) bound for cheap, relative-low-height, power-band stopped tags holds with the hybrid floor. This permits MUCH larger small-label caps than qW without losing that bound. More generally a floor f(B) satisfying f(B) log B=o(B^theta) works in the same counting argument if the budget remains o(X^2).

This is not a bound on the total stopped population: the unremoved classes are p<B^theta (including stops at the floor), large r, or h_now>pH. The finite audits below show that the pure normalized cap puts most of its stops in small labels. In particular it would be misleading to claim it improves total stopping over the original uniform B cap merely because its arithmetic cost is smaller. The original uniform cap remains a separate viable sufficient-route formulation, and the hybrid cap is a partial alternative.

## 5. Exact finite tests of both cap rules and growth/decrease split

Executed in the current runtime the function bodies of:
    node research/min_normalized_first_stop_audit.mjs 256 1024 4096 16384 65536 262144
    node research/min_hybrid_normalized_first_stop_audit.mjs 256 1024 4096 16384 65536 262144
Use fixed diagnostic W=2,4,8, pure cap pW and hybrid cap W max(ceil(sqrt B),p), preserving all original tags and cutoffs. The finite diagnostic modes (Q,F,z,H) are explicit in JSON and may not satisfy the asymptotic separation conditions: e.g. a finite small p can have a reset parent. At every high transfer verify linear identity and low suffix, prior cap, same-tuple mass accounting for comparable-parent valid incidences, possible small-parent congruences and mass upper bound, source conservation, and q>p whenever a stop-tag has nonincreasing mass relative to its prior group. Count group-level single-donor stops separately (not merely individual tags with nonincreasing mass). Verify literal parity-GCD clocks and terminals for X<=1024. The pure-cap script and full data are exact remote readback at 2c632a927ed4573ea92535fe06773c831e93b4d6; hybrid script and data at 0bd6d5b21c9b0093e458f6e31c659023094028b9.

At X262144, B1355, N131072:

|W|pure stopped|pure stopped p<sqrt B|hybrid stopped|hybrid stopped p<sqrt B|hybrid twins|
|--:|--:|--:|--:|--:|--:|
|2|82763|82458|58765|53065|72307|
|4|66435|66435|34194|30492|96878|
|8|45905|45905|12576|11200|118496|

All runs here have zero non-twin terminals. At pure W4: of 66435 stopped tags, 55535 are in a current group strictly larger than their own whole predecessor, 2418 have equal mass, 5640 smaller mass, and 2842 have no preceding high event. 3986 stopped tags are in groups with exactly one nonroot donor and no root injection (all q>p). Example p11,C538572,m54, preceding q17,D538542,m0=54. Same mass, so this is a pure label decrease from normalized 54/17 to 54/11 crossing W4. This directly checks the obstruction to inferring mass growth from normalized mass growth. At hybrid W8, no single-donor stops, 1088660 verified consecutive-high relations, but 12576 stops remain. With finite mode Q=ceil(B^.75)=224,F2,z31,H2, no stopped tags at p>=Q in any of the three hybrid runs; comparable-parent valid transition incidences exist (17 across 3 tuples in each), so the condition is not universally vacuous, though the stop conclusion on these windows is empty. The pure W2 mode Q37,F2 has 305 stopped tags at p>=37, 15 from q<p/2, maximum within-group small-parent fraction 0.07273. The finite outcomes do not establish any of the asymptotic estimates; the proofs of sections2-4 use arithmetic only.

## 6. Next actual proof obstruction

The useful result is now not confined to top-to-top moves: under a hybrid normalized cap, for ANY fixed power threshold B^theta above the floor, small donors are negligible at large-label stops, and the comparable donors with cheap clocks and low relative height have a proved all-depth o(X) source bound. The pure cap's finite data diagnose an important limitation: small-label stops are dominant, and some occur without any increase in actual source mass. Thus a simple monotone normalized-mass argument cannot prove the desired global anti-concentration. One natural next task is to follow large cohorts across low-label intervals using the established LOW barrier with a growing cutoff or physical first-contact certificates, rather than treating every downward label change as a new merge. Need a quantitative bound for actual large-mass formation at floor stops, and/or a bound on the source population with expensive or high-height large-label stops. Neither follows from the present deletion. No new branch, no main changes, no Lean compilation.
