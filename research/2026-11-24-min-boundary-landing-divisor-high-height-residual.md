# Landing-divisor bound for cell stops, high-height residual, and an averaged LOW-cost criterion

2026-11-24 JST. Continues d02888361c6da9749fdad77554adf720139d05af on the SAME research/min-cycle-forest-2026-11-24 branch. Elementary paper deductions from the established barrier-cell full inverse cap and clock-refined variance forest; exact finite diagnostics. No Lean compilation. No complete stopping deficit or twin-prime proof.

## 1. Count landing divisors instead of all possible boundary primes

Keep canonical MIN, original odd sources M in [X,2X), N=X/2, B=ceil(sqrt(7X)), individual K(M), the barrier-cell admission rule and full inverse-prime stop thresholds of the preceding note. Choose Y tending to infinity, L=2 product_(3<=p<Y prime) p, cells (jL,(j+1)L], T=ceil(X/log^2 Y), and tau_p=ceil(B^2/p) for every p>=Y. Require L=o(T), L<=X. Previous estimates give R_pre=O(X^2/log^2 Y) and J_c<=S_c/T<=N/T for stopped cells, J_p<=N/B for prime stops. No twins implies S_c+S_p=N-o(X).

At a stopped cell (J,J+L], every noninitial entry is the result of an executed crossing event (q,A,u) with q>=Y and actual landing horizon C=A+q-1. Thus J<C<=J+L and
    q divides C or C+2.
Indeed q divides A+1 or A-1 respectively. For a fixed C and q the projected crossing key is uniquely determined (A=C-q+1). This is a stronger counting interface for large q than simply allowing at most two keys per q at each boundary: there are only L/2 possible even landing horizons. For sufficiently large X all actual C,C+2 lie in [1,7X+2] (restrict to the actual horizon window, including a partial end cell).

Fix Q>=Y, Q<=B. A positive integer n<=7X+2 has at most log(7X+2)/log Q distinct prime factors >=Q, by their product dividing n. The sum of their reciprocals is at most log(7X+2)/(Q log Q). Sum over C and C+2 at the at most L/2 possible landing horizons. For every stopped cell the number of projected gateways q>=Q and the sum of their reciprocal labels are bounded by
    J_g(cell,Q) <= L log(7X+2)/log Q,
    I_g(cell,Q) <= L log(7X+2)/(Q log Q).
All actual projected gateway masses are <=B^2/q since the crossing event executed under its inverse cap; neither the number of actual clock classes nor the overshoot of the cell admission mass affects this. Therefore
    S_c(q>=Q) <= B^2 J_c L log(7X+2)/(Q log Q)
              = O(X log^2 Y L log B/(Q log Q)).
One may take the minimum of this estimate and the previous band capacity 2B^2 J_c sum_(q>=Q prime)1/q. The landing-divisor estimate does not require the cell boundaries or stopped set to be uniformly distributed mod q. It uses actual landing horizon restriction even if a single high event skips many cells. It also applies to the reciprocal sum in the clock moment theorem; the bound above on S_c is already enough for the following range.

Choose Y=c log log B (integer rounding harmless, Y>=11 eventually) with a sufficiently small fixed c>0. Chebyshev's bound gives L<=log^(1/4) B, and L=o(T). Put Q=ceil(L log B) (eventually Y<Q<B). Then Q<=2 log^(5/4) B, log Q>=log log B. Hence
    S_c(q>=Q)=O(X (log Y)^2/log Q)=o(X).
This improves the previous deletion of nearly-top prime gateways to the entire range from a polylogarithmic cutoff Q up to B. In particular all but o(X) of the noninitial cell-stop tags must have crossing label q<Q. The choice of slower-growing Y is important for the polylogarithmic size of Q; with Y=c log B the same general inequality is valid but Q can be a power of B.

## 2. Small physical classes at small gateway labels must have very high heights

Continue with the above choices. Let a=ceil(log^(1/4) Y), H0=X/log^4 Y. For a projected crossing key (q,A) entering a stopped cell, the actual post-heights h=2u-(A+q-1) are nonnegative and separated by at least 4q. Thus at most 1+H0/(4q) distinct clock classes have h<=H0. If counting only classes with mass <=a, the mass of those classes at that projected key is at most a(1+H0/(4q)). This is a direct counting argument, with no square-root moment loss. The previous at-most-two crossing keys per boundary per q now suffices. Summed over all stopped cells and gateway labels Y<=q<Q, it bounds the total number of original tags in small, low-height physical gateway classes by
    S_c(q<Q, class mass<=a, h<=H0)
       <= 2 a J_c [pi(Q)+ (H0/4) sum_(Y<=q<Q prime)1/q]
       = O(a log^2 Y (Q+H0 log Y)).
In the last step log log Q=O(log Y) from the explicit choices, and the elementary harmonic prime bound. The first term is o(X) since Q is polylog B, and the second is O(X/log^(3/4) Y)=o(X).

At cell-stop entry the attained height is <=6+4R_i. The global prefix budget removes the entire population of tags having any attained height >=H1=X/log Y at a cost O(R_pre/H1)=O(X/log Y)=o(X), by charging each root only once. This deletion is valid even though a tag may have visited many cells. It is also legitimate in the physical-forest variance accounting because terminal variance loss from deleting b original roots is at most b. For a cell physical gateway class, the height depends only on that class, so the entry-height restriction does not split its mass; if one instead removes earlier high-height tags, apply the root-deletion variance lemma rather than reasserting an unchanged class threshold. In the statement below remove high ENTRY heights only.

Root injections at cell stops contribute O(X L/T)=o(X) as before. Consequently all but o(X) of the cell-stop tags fall into one of two classes:
    (i) a physical gateway class of mass >a, with Y<=q<Q;
    (ii) a physical gateway class of mass <=a, with Y<=q<Q and H0<h<H1.
For class (i) we may also restrict h<H1, losing only o(X) tags. Class (ii) has a very large prior height index k=(h-b)/(2q), b=0 or6, in particular k>=(H0-6)/(2Q); this tends to infinity faster than any fixed logarithmic power of B. These are actual attained heights of the crossing event, not normalized heights inferred from a change of label. The global R_pre bound by itself does NOT make class (ii) small: H0 is below the average upper-budget scale X/log^2 Y. This is a reduction of the residual to large-height, small-label, small-physical-class entries, not an anti-concentration estimate for them.

## 3. Combine with prime-stop moments and physical variance

Choose integer D=floor(log^(1/8) Y), eventually >=1, so D tends to infinity, D/a=o(1), and D=o(log^2 Y). Retain all prime-stop tags and the cell-entry tags of class (i) above, and retain their actual high-event paths up to their proposed prime stop or executed gateway respectively. As in the preceding note the clock-refined graph on these retained paths is a forest: same physical high event forces same next high event whenever both tags continue to an accounting stop; a cell stop reached by this event or a prime stop applies to both. Distinct cutoff tags only truncate the paths; neither of two retained stopped tags can naturally terminate before its own endpoint. Physical gateway classes of a given projected key and clock all enter the same stopped cell. Restricting to class (i) preserves entire such classes. There is no assertion that an unrefined projected group cannot split.

The previous prime-stop moment gives total terminal within-clock variance >=S_p/2-o(X) since G_virtual <= O(XD/B+X sqrt(D)/log Y). For the retained cell classes, the hat-kernel estimate F_D(A)>=m/2-D gives
    sum F_D(A) >= S_c(i)/2 - D S_c(i)/a
                = S_c(i)/2-o(X).
Here using merely m>2D with D fixed relative to the class threshold would not justify a negligible deficit; this is why a and D are deliberately distinct growing scales. Total terminal within-class variance equals total true physical merge variance in the retained forest. The harmonic near-flow deletion at d=floor(D/(log(2D))^(1/2+epsilon)) for any fixed epsilon>0 is o(X). Let P_phys,far be its remaining nonnegative far proxy, counting only cross-incoming-group pairs at their first common physical vertex. It is at least (S_p+S_c(i))/2-o(X). Thus on no-twin windows
    S_c(ii) + 2 P_phys,far >= N-o(X).
Compared with the preceding result, the unestimated cell term has been reduced from all sub-nearly-top gateway labels to polylogarithmic labels with small actual physical class and attained heights in (X/log^4 Y,X/log Y). No bound on P_phys,far or on S_c(ii) sufficient for twins has been proved. The distance scale here is only slowly growing (D about (log log log B)^(1/8)), not the large D=B scale of the earlier forest result.

## 4. Alternative: a sufficient averaged LOW-cost criterion to avoid cell stops entirely

This is a separate conditional route; the upper bound is rigorous but the sufficient asymptotic condition is not established. Let Y>=5, L=2 product_(3<=p<Y prime)p. For even C define V_Y(C) as the maximum total r-cost of any finite path of low eligible steps (p<Y, p divides C-1 or C+1, horizon advances by p-1), ignoring clock ordering. This is well defined, periodic mod L, and <=1.5L by the barrier. If a low step is eligible then r(C) equals the least eligible low prime, independent of clocks and B>=Y; if none is eligible the cost is zero. On the cell [0,L] compute the exact recursion backwards:
    V_Y(L)=0,
    V_Y(C)=max(0, max_(eligible p<Y) [r(C)+V_Y(C+p-1)]).
Translation by L preserves the eligibility and costs. Define the mean A(Y)=(2/L) sum_(even 0<=C<L) V_Y(C).

A smaller valid upper envelope is obtained by the low-only deterministic clock ghost: at (t,C) select the earliest next clock among low primes, tie by smaller prime, ignoring all high clocks, continue until no low prime is eligible. Every actual consecutive low-only portion of the full MIN path is a prefix of this ghost from the actual initial t,C: if the full rule chooses a low prime it must choose the same earliest low clock and tie-break. Its cost cannot exceed the complete ghost cost. All clock periods 2p divide L, so the ghost cost G_Y(C,t mod L) is periodic in t and C (translation C by L does not change eligible side). Let V_Y^clock(C)=max_(t mod L) G_Y(C,t); this is <=V_Y(C). Replace A(Y) by its smaller mean if desired. Maximization over phases is necessary for a uniform upper bound because actual high-key mass is not known to be evenly distributed in clock phase. Averaging the ghost over phases instead of taking maxima is not justified here.

Use full inverse prime-only stopping tau_p=ceil(B^2/p) for p>=Y, no cell stops and low p<Y transparent. Initial low costs total O((X+L) A(Y)): the original C0 spacing4 permutes even residues modulo L since L/2 is odd. After an executed high event q>=Y the post-horizon C satisfies q divides C or C+2. For each side the even C lie in a progression of step 2q, which cycles through all L/2 even residues because q is coprime to L. Thus sum of V_Y(C) over the possible post-horizons for fixed q and side is <=O((X/q+L) A(Y)) by counting complete cycles and bounding the incomplete one by a complete nonnegative sum. Every executed projected high key supplies at most B^2/q tags; each one incurs at most V_Y(C) for its following low block. Consequently
    R_lo <= O(A(Y) [X+L+B^2 X sum_(q>=Y prime)1/q^2
                                   + B^2 L sum_(q>=Y prime)1/q])
          = O(A(Y)[X+ B^2 X/(Y log Y)+B^2 L log log(3B)]).
For L<=sqrt B and Y<=c log B the last term is absorbed by the middle term; the first is also absorbed for sufficiently large B. The existing high cost estimate gives
    R_pre = O(X^2 [1/log^2 Y + A(Y)/(Y log Y)]).
The same holds with the clock-max envelope. Hence IF a diverging sequence Y exists with A(Y)=o(Y log Y) (or the smaller clock-max mean has this property), one can choose a slowly growing Y(B) on that sequence with L<=sqrt B and Y<=c log B. Then R_pre=o(X^2) WITHOUT cell stops, and the full inverse cap yields I_p<=N/B^2. All virtual terminal variance is o(X) at some diverging scale D chosen sufficiently slowly that D*(1/log^2 Y + A(Y)/(Y log Y))=o(1) and D=o(B). This would eliminate the cell-stop term by a genuinely different accounting argument. It is not enough for twins by itself because physical merge variance still needs an upper bound. Neither the required A(Y) asymptotic nor any comparable statement about clock phases of actual tags is proved. The finite envelope values below do not support asserting the sufficient condition; the permissive path mean relative to Y log Y increases in the tested range. In particular one cannot use the low-only ghost's average over phases in place of the maximum without proving a new phase-distribution theorem.

## 5. Exact finite audit

Saved research/min_boundary_landing_divisor_audit.mjs and research/min_boundary_landing_divisor_results.json, exact remote readback at b79326de436839b270b46a9041165506ed8d6958. Executed the function bodies at X=256,1024,4096,16384,65536,262144 using the same finite caps as the preceding audit: Y=11,13, L=210,2310, inverse numerator A=max(2,floor(B/4))*B, cell cap T=max(floor(L/4)+1,ceil(X/256)). Both full inverse without cells and combined rule. Retain original conservation, literal clock, boundary-crossing, cell-cost and moment checks. Additional exact landing divisor identity q|C or C+2, uniqueness of (C,q) within cell, factor-product bound, band-specific actual reciprocal sum and mass <=A times divisor bound, and small-class low-height counts <=8 times the number of admissible clock positions. Test several finite Q including ceil(L log B), and three height cutoffs including floor(X/log^4Y). At these small X the analytic Q=ceil(L log B) often exceeds B, so that particular band is empty; tests of other Q are nonempty. The finite cap T is not asymptotic T=X/log^2Y. No numerical evidence that the residual class of the asymptotic theorem is already rare is claimed.

At X262144,Y13, combined rule: S_c16921, 8663 initial injections, 8258 actual crossing tags in132 projected gateway groups. Of these 6856 have q>=37 and2149 have q>=678. The landing-divisor bound holds but is numerically very loose at these parameters. With a=8, 7958 crossing tags in classes >8, 300 in classes <=8. Of the 300, 51 have height>B=1355 and none have height>6056=floor(X/log^4 13). All earlier original paths and source counts unchanged. For Y11 no cell stops at this X. The new asymptotic choices of Y,T,a,D and Q are different from these finite diagnostics.

The same saved script computes the exact permissive LOW cost envelope for Y=5,7,11,13,17,19,23 via backward integer DP, verifying the barrier at every permissible edge. At Y<=13 it also computes the deterministic low clock ghost for EVERY even horizon residue and EVERY t phase modulo L; verify its value never exceeds the permissive envelope. Reported means:
    Y   L        A(Y)       max cost    clock-max mean (if computed)
    5   6        3          6           3
    7   30       8.066667   20          7.133333
    11  210      16.019048  48          13.438095
    13  2310     36.072727  144         25.217316
    17  30030    68.329404  403         not computed
    19  510510   151.158763 1103        not computed
    23  9699690  283.924395 2343        not computed
The permissive ratios A/(Y log Y) are 0.373,0.592,0.607,1.082,1.419,2.702,3.937 respectively. The clock-max ratios at Y<=13 are 0.373,0.524,0.509,0.756. Larger clock-max DP was not run (quadratic memory in L). At Y13 the all-phase mean is14.770232, distinct from the required clock-max mean25.217316. These are exact integer recurrences with rounded display means, not a claim about limiting ratios. The permissive envelope is only an upper bound, so its growth cannot disprove a smaller true LOW-cost bound.

## 6. Next concrete obstruction

Landing-divisor counting removes the entire large-label gateway range q>=ceil(L log B) with the chosen slowly growing Y; small-label, low-height small clock classes also have negligible mass. The remaining cell population requiring a new argument consists of small physical classes with polylogarithmic gateway primes and heights in a narrow near-X logarithmic range. A direct continuation is to trace those tags back to their first attainment of a high height, and use the exact height increment 2 wait-(p-1), rather than charging all elapsed cost. The present budget alone does not give the needed smaller-height deletion. Alternatively prove a better averaged low-cost envelope, but the present finite envelope test has not established that condition. The physical far-merge upper bound remains necessary on either route. No new branch, no main edit, no Lean compilation.
