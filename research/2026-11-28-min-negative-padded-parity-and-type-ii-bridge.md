# A padded parity obstruction for the 5/16 bridge, anti-padding on the true source, and a sharpened Type II target

2026-11-28 JST. Issue #10. Continue 4708dfc8201f9445cd391f235cc2025d22aa8936. User asks continued research toward M85 until the next Astra run. New results: (1) explicit weighted countermodel satisfying even absolute-error sifting data at every fixed level <5/8 but with both target roughness >5/16 and the previous positive correction identically zero; (2) an additional unconditional arithmetic restriction of the actual asymmetric semiprime source ruling out all near-3/8 padded countermodels of this kind at the relevant roughness; (3) a larger explicit correction rectangle, with rigorous numerical normalization and a specific Type II comparison sufficient for an exponent above 5/16; (4) extension of the earlier growing-depth actual-path theorem to either first-firing sign, and a density-scale alternative if the new static target fails. M85 and >5/16 density lower remain OPEN. This is not a proof of a general impossibility of switching or a classification of all sieve extremizers. No new Lean run or independent specialist review.

## 1. Primary-source check and reason to change approach

Reopened:
- K. Matomäki and S. Zúñiga-Alterman, Weighted sieves with switching, arXiv:2405.19063v3 (14 March 2025), https://arxiv.org/pdf/2405.19063, pp9–10 equations (16)–(19), page images. Switching with positive parts of weights is useful when the switched sequences have appropriate distribution; its abstract theorem does not supply the required lower for two specified factors of a shifted semiprime. A positive correction cannot simply be replaced by its predicted density.
- Z. Yang, arXiv:2608.13299v2, https://arxiv.org/pdf/2608.13299, pp2–4,25, (1.2),(1.3), Theorems1.1,1.2,1.4 and (4.12)–(4.13), page images. The high level for nu>3/8 concerns a free integer l and a prime p, with d in (1.2) an appended modulus factor, NOT a divisor of the free variable. It does not permit replacing l by a prime or rough sequence. Trying to expand the prime indicator of the longer variable via a convolution would still leave configurations where all free variables are short (e.g. two factors of size ~R^(.3125) in the long factor R^(.625)); the new Type II estimates for these are not supplied by Yang. No claim that a future such extension is impossible.
- A. Pascadi, arXiv:2505.00653v2, https://arxiv.org/pdf/2505.00653, pp21,24, screenshots, (4.16),(4.17), definition of well-factorable Iwaniec components. Reconfirms 5/8 ceiling of the sufficient dispersion system. We continue to use the previous two-factor slice for actual lower estimates; constant Q3=1 endpoint interpretation still listed for independent review.
- J. Maynard, Counting primes, ICM 2022, DOI10.4171/ICM2022/206, https://www.mathunion.org/fileadmin/IMU/Prizes/Fields/2022/jm.pdf, §§3–3.1 Lemma6, §6 discussion of Harman sieve and Question20; PDF text and page image inspected. T. Tao, 254A Supplement 5 (29 Jan 2015), https://terrytao.wordpress.com/2015/01/29/254a-supplement-5-the-linear-sieve-and-chens-theorem-optional/, §1 Optimality: classical parity examples and Liouville PNT for the needed error control. The weighted and padded adaptation below is a deduction for the particular local model g(p)=1/(p−1), the size R and correction rectangle in our research, not a novelty claim about the classical parity phenomenon.

## 2. Explicit weighted padded parity countermodel

Fix a constant level exponent d0<5/8, and let the sifting prime cutoff be at most R^.35. Put L=log R, X=R^(5/8), Y=R^(3/8), and fix e.g. eta=.05. Take odd integers m in [X,(1+eta)X] and primes ell in [Y,(1+eta)Y], so j=m ell in [R,2R]. Put lambda(m)=(-1)^Omega(m) (Liouville), and define
  w(m)=prod_{p|m, p odd}(p−1)/(p−2),
  a_j=sum_{m ell=j} w(m)(1+lambda(m)),
where the sum is over these boxes only. The weights are nonnegative, finite support. Multiple representations are allowed (at most two ell in the box for large R); this is an artificial sieve sequence, NOT the indicator of actual shifted semiprimes. It has weighted mass X_R=sum a_j comparable to R/L, as in the actual asymmetric seed.

**Claim.** For every fixed A>0,
  sum_{d<=R^d0, d odd squarefree, P^+(d)<=R^.35}
      | sum_{d|j} a_j − X_R/phi(d) | <<_A,d0 R/L^A.       (1)
Thus even an absolute-value remainder estimate, stronger than the previous well-factorable remainder control on this set of moduli, coexists with zero target rough count. We do NOT claim (1) for moduli containing the padding primes ell>R^.35.

Proof: Since ell>R^.35, d|j iff d|m. Define h(e) multiplicative, supported on odd squarefree e with h(p)=1/(p−2), and h(1)=1. Then w(m)=sum_{e|m}h(e) and
  C=prod_{p>2}(1+h(p)/p)=C2^(-1), C2=prod_{p>2}(1−1/(p−1)^2).
The product converges absolutely. For odd squarefree d and k odd, w(dk)=w(d)sum_{e|k,(e,d)=1}h(e). Set T=X/d>=R^(5/8−d0), a fixed positive power. Counting odd multiples in the interval k in [T,(1+eta)T] gives
  sum_{d|m} w(m)
   = (eta X/(2d)) w(d) prod_{p>2,p not|d}(1+h(p)/p)
     + O(w(d)[T^(.5)+L^C1]).
Indeed the floor remainders are bounded by w(d) sum_{e<=2T}h(e) << w(d)(log(2T))^C1, by Euler product (h(p)=1/p+O(1/p²)); the main tail uses sum_{e>T}h(e)/e << T^(-.5), since sum h(e)/sqrt(e) converges. Constants may absorb endpoint rounding. For each odd prime p,
  [w(p)/p]/[1+h(p)/p] = (p−1)/(p(p−2)+1)=1/(p−1).
Thus the main term is C eta X/(2 phi(d)).

For the parity part use complete multiplicativity:
  sum_{d|m} w(m)lambda(m)
   = w(d)lambda(d) sum_{e<=2T,(e,d)=1} h(e)lambda(e)
       sum_{k' odd in [T/e,(1+eta)T/e]} lambda(k').
The classical Liouville PNT gives O_A(U/(log(2U))^A) for a partial sum through U; restriction to odd arguments follows by subtracting the even contribution, equal to minus the unrestricted sum through U/2. For e<=sqrt T, log(T/e)>>_{d0}L, so the total is O_A(w(d) T/L^A). For e>sqrt T the trivial bound O(T/e+1) and convergent sum h(e)/sqrt(e) give O(w(d) T^(.75)). Therefore, uniformly in d, the unnormalized count of m is
  C eta X/(2 phi(d)) + O_A(w(d) X/(d L^A)).
Multiply by #ell~eta Y/log Y. Sum d using sum_{d<=R^d0} w(d)/d << L^C2 (only squarefree terms needed), choosing the arbitrary log exponent larger. The same estimate at d=1 replaces the leading total by X_R, with an additional sum of 1/phi(d)<<L. This proves (1).

**Roughness obstruction.** Every positive-weight m has even Omega(m)>=2 since m>1; hence P^-(j)<=P^-(m)<=sqrt((1+eta)X). For any fixed b>5/16, S_model(R^b)=0 for sufficiently large R.

**Exact failure of the previous positive term.** For the original correction q exponent t in [.24,.28], r exponent u in [.13,.16], both primes must divide m, since ell is larger. If j is r-rough, the residual k=m/(qr)>1 (t+u<=.44<.625) is also r-rough. But k<r² for large R because t+3u>=.63>.625. Thus k must be prime, contradicting even Omega(m)=Omega(qrk)=3, including repeated-factor cases. Consequently J_model=0 exactly for sufficiently large R. The same reasoning applies to the expanded rectangle in §4, with t+3u>=.626>.625. It also implies zero for the preceding three-appended-prime switched sector: q1q2q3 has exponent U in [.565,.5979], so m/(q1q2q3)>1 but exponent <=.06, strictly below the least allowed factor q3 (>=.165). It cannot be q3-rough. So the improved upper bound for that sector is satisfied too.

This establishes a logically precise limitation: any argument for positive J or >5/16 using only nonnegative weights supported in [R,2R], the local sifting data (1), the exact Buchstab identities and the single preceding reverse-sector upper bound cannot succeed for all sequences satisfying those inputs. This is NOT a claim about the full arithmetic hypotheses of Pascadi, the actual shifted semiprime sequence, or all possible switched estimates. The auxiliary factors are deliberately outside the set of sifting primes. Neither finite numerical searches nor further depth of identities alone can eliminate this witness.

## 3. An actual arithmetic estimate distinguishes the artificial model

Return to the real source n=pv in [R+1,2R+1], p and v prime, with p in the fixed band [R^.374900,R^.374950], as in 4708dfc. Let m=n−2, a_m^real=1 for this uniquely represented source, B_R its mass, M_R=4 C2 B_R/L. In fact the following upper is uniform for p in any fixed band [R^nu0,R^nu1] contained in [.37,.38]. Fix any roughness alpha>.20, e.g. alpha=.24 or .312, and any interval of prime factors q in [R^(.375−delta), R^(.375+delta)], delta<=.005, or any narrower interval there. For fixed p,q, if q|m then p!=q, and
  p v − q u = 2,   v and u=m/q both R^alpha-rough.
Here v is prime of exponent >.62, and u is rough because m is. The integer solutions lie in one progression v=v0+q t, u=u0+p t with parameter interval length O(R/(pq)+1) and polynomial lower scale R/(pq)>=R^.24. Two affine forms have distinct roots modulo every odd small prime not dividing pq, by the determinant identity. Small fixed-factor exclusions (2,p,q) cost a uniformly bounded factor. Ordinary dimension-two upper sieve on this parameter at cutoff a small fixed power of R (e.g. R^.01), level a small fixed power of the interval length, gives O(R/(pq L²)) solutions, uniformly; interval CRT remainders O(2^omega(d)) are negligible at a sufficiently small polynomial level. No deep prime distribution required here. Summing over the two prime factors,
  # {actual source m R^alpha-rough, has q in band}
    << R/L² (sum_p 1/p) (sum_q 1/q).                   (2)
The source main mass satisfies B_R~(R/L) integral_{nu0}^{nu1} dnu/[nu(1−nu)] for a fixed positive-width band by PNT/partial summation. Hence normalized by M_R, (2) is O(delta)+o(1) for the symmetric exponent band of width 2delta; constants uniform in such fixed small widths (asymptotic threshold for R may depend on them). For a single multiplicative interval [Y,CY] with fixed C, the upper is O(R/L³), o(M_R). More generally a window with log ratio o(L) gives o(M_R) by PNT/Mertens and dyadic prime harmonic bounds, uniformly near exponent .375.

On the other hand the actual lower at alpha=.24 from the prior two-factor slice is >>M_R. For alpha=.312 (<.6246/2) it remains >>M_R with a smaller fixed positive constant. So after removing every such padding-window point, the real source still has >>R/L² rough points. For a sufficiently small fixed delta, the symmetric exponent band can also be removed while retaining a positive fraction of that lower. Since alpha>.20 implies that a divisor in the indicated .375 band must be prime, this also eliminates any factorization of an R^alpha-rough m with one factor in that band and the other correspondingly near R^(5/8). Thus ALL the padded model points from §2 that survive alpha-roughness are excluded by (2); the artificial sequence does not satisfy this extra estimate. The model itself has a positive alpha-rough mass by ordinary lower sieve using (1) at any fixed level between 2alpha and .625 (choose alpha=.24 or .312). This distinguishes the two models at density scale.

Possible new approach: a quantitative inverse/stability result for the linear-sieve lower bound at its critical threshold under a no-near-3/8-divisor condition could turn (2) into a strict positive lower. Such a stability result is not established; excluding this one family of extremizers does not classify or exclude all zero-roughness sequences. Maynard's survey §6 discusses the general inverse/optimality issue for stronger sieve information; no applicable theorem found in the inspected sources. In particular we do not use the exclusion of the padded model as a proof that J_real>0.

## 4. Broaden the correction and isolate a single Type II comparison

Retain d=.6246, forward capacities .3748,.2498, a0=.24, target b0 in [.313,.35]. The previous one-prime upper/lower argument from 4708dfc gives ordinary coefficient log((d−b0)/b0)/d. For q exponent t in [.236,.300] and r exponent u in [.130,.200], use
  S_q(q)=S_q(R^.13)−sum_{R^.13<=r<q} S_qr(r).
The ordinary upper of S_q(R^.13) still costs the SAME coefficient as for S_q(q) because (d−t)/.13 ∈[1,3] throughout. If q<a0 (only the small subband [.236,.24)), this q does not occur in the original subtraction at a0=.24. Therefore use the lower base cutoff a0=.236 INSTEAD: d/a0 in (2,4), all q∈[a0,b0] can be appended, and the telescoped ordinary coefficient is unchanged. This explicit adjustment is necessary; we do not add corrections for q outside the original sum. Sifting upper cutoff q may be replaced by just below R^(d−t) for t>d/2, with arbitrarily small fixed slack, as in the previous note. The two remainder factors and squarefree mask are as there; append q in first capacity, use residual capacities and multiplicative boxes with slack. Hence retaining any nonnegative subset of the expanded correction yields the corresponding lower.

In particular count the subset
  K_R = # { p v − 2 = q r s, all five variables prime,
             p in actual source band,
             .236<=log_R q<=.300,
             .130<=log_R r<=.200,
             R+1<=pv<=2R+1 }.
Here s is automatically >q>r at polynomially separated scales (exponent 1−t−u>=.5), so the right product is squarefree and contributes exactly once to the expanded correction. No repeated representation issue. Thus
  S(R^b0)/M_R >= log((d−b0)/b0)/d + K_R/M_R − epsilon   (3)
in the same fixed-slack asymptotic sense. No actual lower on K_R is proved here. Note that the whole expanded rectangle has d−t−u<2u, and the padded model still has zero correction; ordinary lower estimates cannot provide a positive K_R.

Define a dense reference sequence, for odd j∈[R−1,2R−1],
  b_j = (2 B_R/(C R)) w(j), C=C2^(-1),
and 0 otherwise. This choice matches the local model and total mass up to o(B_R), not an assertion of true distribution in every factorization pattern. For the same triple-prime factorization q r s, all factors exceed R^.13, so w(qrs)=1+o(1) uniformly. By PNT and partial summation the reference count K_ref weighted by b_j satisfies
  K_ref/M_R -> I = (1/2) integral_.236^.300 integral_.130^.200
                      dt du / [t u (1−t−u)].
This follows because for fixed q,r the prime s interval has length R/(qr)+O(1), its logarithmic exponent is 1−t−u, and reciprocal prime sums tend to integrals dt/t and du/u. Constants 2B_R/(C R) and 4C2 B_R/L give the factor 1/2. Endpoint rounding has vanishing mass. No independent-prime assumption for the actual source.

An explicit sufficient new estimate, **OPEN**, is the following bilinear comparison on the shifted integer j:
  sum_{k s in [R−1,2R−1]} alpha(k) 1_prime(s) [a_real(k s) − b_(k s)]
       >= −(1−eta) I M_R + o(M_R),
where alpha(k)=1 iff k=q r for the two fixed disjoint exponent ranges (unique representation), 0 otherwise, k exponent in [.366,.500], and a_real(j)=1 iff j+2 is the actual semiprime source. This is a single shifted-product Type II correlation (or just its one-sided lower), not the already-known weighted congruence remainder. It is weaker than a full asymptotic for that correlation, and a precise target for a new dispersion/switching method. We cannot quote Yang's free-integer theorem for this prime s weight or claim that the usual Type II moduli theorem is the same estimate.

The exact audit uses monotone Riemann sums with grid .0001; the integrand decreases in both variables since 1−2t−u>0, 1−t−2u>0. Outward-rounded integer arithmetic certifies
  .090728634033055701 <= I <= .090787271937214242.
Also exact bounds for log(b0/(d−b0))/d via positive atanh series with geometric tail give thresholds:
 b0=.313:  .007177195875056104 (upper), eta>.0791062 suffices;
 b0=.315:  .027684113208551128, eta>.305131 suffices;
 b0=.320:  .078965026149072720, eta>.870343 suffices.
For example eta=.10, .32, .90 respectively gives a positive fixed slack in (3), proving >>R/L² real canonical roots reaching first height floor(R^sigma) with G=0 for all fixed sigma<b0; use sigma=.3129 for an explicit >5/16 result if b0=.313. The expected full reference coefficient alone would only carry this particular bridge to ~.32115, not .4. The preceding smaller rectangle required much higher fractions. These are rigorously certified implications of a future lower estimate, NOT a numerical prediction that eta holds. The actual source has no known such lower yet. This concretely locates the new information needed, rather than trying increasingly deep ordinary Buchstab identities on the same data.

## 5. Use the true asymmetric source for actual-path transport in the complementary case

Generalize the growing-depth theorem of 4f654dfe616a0e0d88048ecf5d67bbe68944d8ef from all-plus first events to arbitrary first signs, under exactly the same hypotheses except the first-sign restriction. We give the necessary changes, keeping the same bounds and proof:
  A+s0=pv, s0=+1 or -1, x0=A-p+1=p(v−1)+c0, c0=1−s0.
For plus the prior canonical wait formula holds and postheight is 0 or p. For minus the birth n=(5−pv)/2 and next odd clock residue p+2 give w0=(3p−1)/2 if v=1 mod4, else (p−1)/2, and h0=3 or p+3. These are the first winner's actual wait (if it wins by definition), obtained from its first positive calendar opportunity. Thus h0=mp+b_s0 with m∈{0,1}. For a signed low word with total gain g to y, the initial spatial pin is y+g=c0 modp; the source forms become
  v=(y+g+p−1+s0)/p,   A−s0=y+g+p−1−s0.
The other low pins are unchanged. In the four-form rough endpoint sieve their undivided shifts and ±1 are distinct (p>>g+1). All CRT moduli and reciprocal word weights unchanged, with constant sign factors. The fast-large interruption pin is still r | 2h0+2u−g+1−2b. A repeat r=p is impossible: y+t≡c0−g+t modp with t=±1; g even, small, and c0+t∈{−1,1,3}, so no equality modp when g<<p. For pair energy, even if two first labels coincide and signs differ, the two initial destinations of a potential contact are within kZ (or kZ+4J for the buffer) and are congruent modulo p to c0,c0'. Their difference must be c0−c0'∈{0,±2}, which equals the difference of the canonical roots because p is the same. A nonzero such difference contradicts 6|A,A'. Hence same prime cannot occur for distinct close roots, even with opposite first sign. For different p, four source neighbor shifts remain distinct by canonical 6-divisibility; mixed signs introduce no additional degeneracy. The previously proved roughness exclusion, fast-large exclusion, pair bounds O(R L^(−4+c+o(1))) and O(R L^(−4+2c+o(1))) and the buffered version follow exactly as in 4f654dfe. This is a paper extension, no new kernel verification.

Apply to the true asymmetric seed at alpha=.312 (sieve level .6246) after removing the padding band of §3 (small multiplicative interval suffices). There are >=c R/L² roots for some fixed c>0 with qmin(A)>=R^.312, A+1=pv and p>=R^.374900. Fix b=.320 (or any .313<=b<=.35). Either >=c R/(2L²) of these roots also have P^-(A−1)>=R^b, giving the new stationary exponent lower for all sigma<b, or >=c R/(2L²) have least opposite factor q∈[R^.312,R^b). In the second alternative q<<p; the first minus event occurs no later than (3q−1)/2 and every plus candidate waits at least (p−7)/2, so the actual first winner is minus with label p0 between q and 3q, age <=(3q−1)/2. In particular the first gain is at least R^.312−1, and all roots are non-twin. Choose theta=.312,rho=.14 (upper 1/2−rho=.36>b) in the mixed-sign extension, k=floor(c1 logL/loglogL) for fixed 0<c1<1. Retain >>R/L² actual roots through k additional events, all visited positions disjoint across roots, every postfirst center non-twin; total >>Rk/L² distinct visited positions. Age <=2R^b, extra event suffix subpolynomial. Initial plus and minus analysis unified for later use; no positive lower for the high postheight type alone. This alternative applies without assuming a global absence of twins. It advances use of the asymmetric seed even if the new static proof fails, but does NOT give first height R^.4.

## 6. Verification and scope

Executed ECMAScript audit research/lean/negative_min_padded_parity_and_bridge_audit.mjs @5af95fa2b26bb3d65e6625371f85f7e282333843 blob ff8987d13b1fa4170686c93e5e992d5fa5da3a06, exact pinned+branch readback. 1228 exact local-density rational checks,22650 multiplicative-weight identity checks; finite core M100000,padding prime1009,5000 odd starts,2509 even-parity, no rough target,68 qualifying q,r factor/size controls and zero J,280 switched triple impossibility controls. These use finite analogues of size conditions, not asymptotic distribution tests. 448000 integer interval cells with outward rounding for I, exact log tail upper; thresholds certified as above. Actual roots scan240001 in [60000,1500000],5647 asymmetric semiprime-plus proxies with P0 in [101,401], q>=11,4q<P0; every first winner minus,112473 literal tick checks,5647 postpins,13729 no-repeat controls,8267 subsequent small-word controls,2391 high and3256 reset (finite proportions only),212 same-prime mixed-sign close-pin cases. Initial scratch JS duplicated variable name high and failed syntax; renamed integral upper variable and executed final audit successfully. The finite tests do not establish the asymptotic proofs or actual Type II lower. No new Lean compile, human specialist review, or >5/16 lower. Both current paper note and audit committed to target branch only. Main and sibling lanes unchanged.

Next high-value tasks: (i) attempt the one-sided shifted product Type II estimate in §4 (rather than repeating the original narrower J), possibly by bilinear correlation/dispersion or comparison with an actual semiprime source of opposite parity; (ii) investigate a rigorous sieve stability theorem using actual anti-padding (2), or stronger arithmetic information that excludes other extremizers; (iii) use mixed-sign paths in a genuinely long-range transport lower, not just first-event count. Goal M85 remains H=floor(R^.4), >>R/L² first-H sinks, gain<=4H, or a stronger direct twin sufficient condition. No claim of 4.85.
