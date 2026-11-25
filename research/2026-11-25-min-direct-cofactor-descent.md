# Direct cofactor primality and the square-entry gate

Continuation of [30538f5](https://github.com/tara-sooo/A166944-Lean/commit/30538f5ccd69237e827c84ed3b128fa2fa3ce504) on the independent direct arithmetic MIN branch. This note uses only the deterministic first-hit/least-label rule, divisibility and elementary integer inequalities. Paper deductions plus exact finite diagnostics, not Lean kernel-checked. No cost decomposition, source-energy assumption, distribution assumption, or claim of external novelty. Twin infinitude and the original A166944 conjecture remain OPEN.

## 1. General cofactor primality from the actual winning clock

Let (t,C) be an adaptive MIN state, C even >=4. An event at n=t+w with label p (odd prime) has side s=-1 for even n, +1 for odd n. Put q=(C+s)/p, Z=C+p-1, d=2t-C, delta=2n-Z. Then

    q odd, q>=p,
    Z=p(q+1)          if s=-1,
    Z=p(q+1)-2        if s=+1,
    2w=p-1+delta-d.

The adaptive eligibility p^2<=C+1 implies q>=p on both sides (for minus, p^2<=pq+2, with p>=3). If q is composite with least factor r<p, then r divides the same neighbor and is in the adaptive pool. Its first strictly subsequent hit is within 2r ticks. It would win a tie at n, so actual p winning implies

    w<=2r-1,
    d>=p+1+delta-4r.                                      (1)

In particular if q<p^2 and d<p+1+delta-4 floor(sqrt(q)), q is prime. This works for arbitrary actual plateau starts, both sides, and for a fixed cap that contains p; q>=p is specific to the adaptive eligibility condition. The conclusion is about the cofactor of the PRE-event neighbor, not primality of Z±1. It needs the first-hit rule; bare divisibility does not suffice.

## 2. Minimal opposite-parity cofactor gives twins, with a sharper converse gate

For an even-side arrival at deficit delta=0, n even and Z=2n imply q+1=2n/p is divisible by 4, so q=3 mod4. For an odd-side arrival at delta=6, n odd and Z+2=2(n-2) imply q+1=2(n-2)/p=2 mod4, so q=1 mod4. Thus on the even side when p=1 mod4 and on the odd side when p=3 mod4, the smallest possible q>=p is q=p+2. (The opposite p classes allow q=p; no twin inference there.)

In the minimal case q=p+2, the prestate and arrival are exactly

    even side: C=(p+1)^2,   Z=p(p+3),   n=p(p+3)/2,   delta=0;
    odd side:  C=(p+1)^2-2, Z=p(p+3)-2, n=p(p+3)/2+2, delta=6.

Suppose p>=11 and q=p+2 is composite; write r=minfac(q)<p. At the arrival tick, n (even side) or n-2 (odd side) is p(p+3)/2, congruent to -1 mod r. Its parity is respectively even or odd. The nearest strictly earlier same-side r-clock is exactly r-1 ticks before n: for the even side, subtract the even residue r-1 to reach 0 mod 2r; for the odd side, n-2=2r-1 mod 2r and subtract r-1 to reach r mod 2r. Thus if p really wins, the prestate must start AT OR AFTER that earlier hit:

    w<=r-1,
    d>=p+1+delta-2r
      >=p+1+delta-2 floor(sqrt(p+2)).                       (2)

This sharpens (1) by almost a factor two for the minimal multiplier. In particular any minimal arrival satisfying

    d<p+1+delta-2 floor(sqrt(p+2))                          (3)

already certifies the twin primes p,p+2. The poststate need not have prime neighbors. The proof is contrapositive: if q is composite its smaller clock excludes the specified early plateau start.

Under finitely many twin primes, for all sufficiently large p every actual minimal arrival of either specified type must satisfy (2), in particular w<=sqrt(p+2)-1. The only way to arrive at the minimal multiplier without extracting twins is to enter the square (or square-minus-two) plateau shortly before the large label fires, with deficit d close to p. This is a direct arithmetic restriction with no accumulated cost.

## 3. One more exact step backwards

Suppose the prestate C in section 2 was itself produced by an actual preceding event with label l and side a, at t. Let x=p+1. For the same side a=s, l divides x^2, hence l|x, and the two event-clock congruences give w= -1 mod l with w positive even. So

    l | p+1,   w>=l-1.

If q=p+2 is composite and p wins, (2) gives l<=r; since l|p+1 and r|p+2 they differ, hence

    l<r<=sqrt(p+2).                                        (4)

Consequently any such minimal arrival with a same-side preceding label l>=floor(sqrt(p+2)) certifies twins (l<r cannot hold). More sharply, given q composite it must be preceded on that side by a prime factor of p+1 strictly smaller than minfac(p+2). This is independent of the starting deficit. It does not assert that every preceding event has the same side.

For the opposite side, exact congruences instead give

    target even, previous odd: l | (2w+8)^2+2;
    target odd, previous even: l | (2w-4)^2-2.              (5)

For the first, l|C+2=x^2+2 and l|(t-2); since 2n=x^2+x-2, obtain x=2w+8 mod l. For the second, l|C=x^2-2 and l|t; since 2n=x^2+x+2, obtain x=2w-4 mod l. Neither integer is zero. Combine with w<=r-1 to constrain the previous label arithmetically. E.g. a gap w=1 in the second case would force l|2, impossible for an odd label. In the first case w=1 allows l in {3,17}. The abstract two-step example in section 7 shows that l=17 can actually occur in the relaxed phase-space setting even when r=3, so (4) cannot be extended blindly to opposite sides.

## 4. Extracted twin pairs are not terminal twins: a forced 3

If q=p+2 is prime in section 2, p>=11 is a twin-prime lower member, hence p=2 mod3. On the even side Z=p(p+3)=1 mod3, so 3 has an eligible minus clock at gap 4 from the even reset (see previous note). On the odd side Z=p(p+3)-2=2 mod3, the plus 3-clock is also at gap 4 from t=Z/2+3.

In both cases no other prime fires earlier. Even side: the only possible earlier competitor is the minus 5-clock at gap 2; p(p+3) is never 1 mod5 (check residues 0..4), so it is absent. Odd side: the only candidates earlier than gap 4 are the plus 5-clock at gap 2 and minus 13-clock at gap 3, using the previous note's shifted phase table (and checking the small wrapped clocks for 3,5,7). The plus 5 requires p(p+3)=1 mod5; the minus 13 requires p(p+3)=3 mod13, whose discriminant 21=8 mod13 is a quadratic nonresidue. Both are impossible. A tie at gap 4 cannot beat 3. Therefore in either case the next adaptive event is exactly label 3 at wait 4.

This explains why the new direct witness is invisible to a search restricted to terminal quiet intervals: a certified twin pair p,p+2 extracted from the pre-event factorization is followed by a short forced transition rather than a long terminal plateau. The claim is conditional on q prime; no converse from the next label 3 is asserted.

## 5. Canonical first-event special case: exact near-square competition

For an odd canonical root M, t=M+2=C/2+3, an even-side first arrival at delta=0 has p=1 mod4, p>=13, w=(p-7)/2, and C=pq+1. If p>=37 and 9q<p^2, q must be prime: otherwise r<=sqrt(q)<p/3. For r>=11 its minus clock at the canonical root is at most (3r-7)/2<w; for r<=7 it is at most 2r<=14<w. This improves the generic 4 sqrt(q) gate at a canonical root.

For q=p+2 and p>=53, p=1 mod4, take the exact candidate root

    M=(p(p+2)+3)/2, C=(p+1)^2, B=floor(sqrt(C+1))=p+1.

The canonical MIN first event is p if and only if
    (i) p+2 is prime, and
    (ii) U=p(p+2)+2 is prime OR U=a*b with a<=b both primes =3 mod4 and 3a>p-6.

Proof: (i) follows from the cofactor lemma; if true, the minus side has no other eligible prime. A prime U is out of the pool. If composite, every eligible prime r<=p+1 of U that is 1 mod4 either r=p (does not divide U), r=p-4 (would divide 26, impossible at p>=53), or r<=p-8 (beats p by its plus clock; small r checked by 2r bound). An eligible r=3 mod4 with r>=11 has plus clock (3r-1)/2 and beats or ties p iff 3r<=p-6; small r<=7 beats p. Thus all prime factors of composite U exceed (p-6)/3, and ((p-6)/3)^3>U for p>=53 (expand p^3-45p^2+54p-270>0). There are exactly two factors; the least is 3 mod4, and U=1 mod4 forces the other also 3 mod4. Conversely both such factors have no earlier clock. The proof for p>=53 is uniform; the code also checks p=37,41 when applicable, without a separate uniform small-p claim.

This exact restriction shows why forcing every near-square candidate to win would be false even assuming many twin pairs: the extra quadratic neighbor can block the clock.

## 6. Further direct terminal improvement for very balanced multipliers

An even reset Z=pm with p odd, m=0 mod4, and a=m-p>0 has half-integral A=(p+m)/2. Assume a^2+5<2(p+m). Put h=(p+m+1)/2. Then

    (h-1)^2 < Z-1 < Z+1 < h^2.

Every composite odd Z±1 has a factor pair u<=v, u,v odd, hence integer midpoint H=(u+v)/2>=h. With product fixed, u=H-sqrt(H^2-(Z±1)) decreases as H grows (equivalently u=(Z±1)/(H+sqrt(H^2-(Z±1)))). Thus

    minfac(Z±1) <= R=h-ceil(sqrt(h^2-(Z+1))).

If either neighbor is composite it has an adaptive eligible clock by floor((3R+5)/2) ticks (phase table of even resets), yielding a sharper sufficient quiet certificate at these balanced multipliers. For fixed a and p large, R=p-sqrt(p)+O(1), rather than floor(sqrt(Z+1))=p+O(1). This is additive O(sqrt(p)) improvement, not an asymptotic constant-factor change. Also any odd prime r dividing Z±1 satisfies, writing u=r-p,

    r | u(u-a)±1,   |u(u-a)±1|>=r

because u is even and the expression is nonzero. These modular and square restrictions do not by themselves force an actual long quiet tail. In fact section 4 shows that the minimal twin-extracting case cannot have one.

## 7. Exact finite diagnostics

Two independently reproducible scripts with verified remote readback:

- [min_direct_balanced_reset_audit.mjs at 15abb1c](https://github.com/tara-sooo/A166944-Lean/blob/15abb1ce0018775f89aea28ad40fb78d1d07bac8/research/min_direct_balanced_reset_audit.mjs), blob 8ec31cb592d1d5d39c73e3e82a513ed963a4e7aa.
- [min_direct_cofactor_history_audit.mjs at 7885dd6](https://github.com/tara-sooo/A166944-Lean/blob/7885dd689cb5897cac1de829e07d211fcdb4c995/research/min_direct_cofactor_history_audit.mjs), blob e33dbfd40c9d741c9124efec82078277fbfe4122.

Run from repo root:

    node research/min_direct_balanced_reset_audit.mjs 1000000
    node research/min_direct_cofactor_history_audit.mjs 100000 24

Executed the actual ECMAScript audit functions in the tool runtime, not a separate Node process. First audit checks all odd M=7..10^6 (499997 roots, 78495 prime roots), exact adaptive clock jumps by SPF, crosschecked against literal tickwise GCD for 5330 first/reset comparisons at M<=10000. 37312 even first resets (8324 prime roots), 2167 strengthened cofactor checks, 1818 generic checks, 174005 modular factor checks, 39 near-square cases and 72 associated composite-neighbor factor bounds. All assertions pass.

Four actual first-event minimal even resets: p=149,269,569,1289; roots M=11251,36451,162451,832051 respectively; first three roots prime. All four have q=p+2 prime, both post-neighbors composite, and next event p=3,w=4. Over p=1 mod4 candidates p>=13 with M<=10^6, 24 have p+2 prime but 20 of these lose the first-clock competition; all 85 with p+2 composite lose. The earlier semiprime obstruction persists: 26 actual even first resets have both neighbors composite in the previous note's shorter quiet regime, including 5 prime roots. Even with m<=4p and 9(m-1)<p^2 there are 2 actual cases (none with prime root in this range). Example M=54211, p=181, m=600, q=599 prime, Z=108600, Z-1=131*829, Z+1=223*487, 195 quiet ticks; this refutes a general elimination of both semiprimes merely from balanced m and prime cofactor. The 39 stricter near-square cases contained no such simultaneous semiprime case in this finite range, not a theorem.

Second audit follows the actual adaptive trajectory of each odd M=5..100000, up to 24 nonunit events or earlier stop. It checks 703591 event incidences, 33651 generic prime-cofactor cases, 54382 composite late-entry cases, and 1876401 backward-clock comparisons. It finds 51579 even delta=0 and 67588 odd delta=6 reset incidences. Ten minimal even incidences for p>=11, seven twin-extracting and three composite-cofactor incidences; no minimal odd incidence in this finite canonical scan. Counts are incidences, not distinct physical states. All eight same-side predecessor checks pass; three are the composite exception. In particular PRIME root M=50387 reaches the actual counterexample to dropping the deficit condition:

    preceding event: t=50718, label 3, C=101124=318^2;
    next event: n=50720, p=317, q=319=11*29, w=2,
    d=312, Z=101440=317*320, delta=0.

The same final edge is visited by M=50381,50389. The exact bound d>=317+1-2*11=296 holds; the previous label 3<11. Thus even prime roots and the minimal multiplier do not suffice without an ancestry/entry restriction.

Separate ABSTRACT phase-space tests (not canonical root histories) enumerate p<=500, all valid plateau starts within 2p of each prescribed arrival, and eligible preceding events with one-tick start. Final corrected run restricts every label to odd primes and asserts even horizons; an intermediate abstract diagnostic inadvertently admitted label 2, corrected before this checkpoint. The actual canonical checks were unaffected. 91 target primes, 416 possible starts (164 composite cofactor, 252 prime, 71 odd-side), 85 actual same-side two-edge abstract controls (19 composite), 2 opposite-side controls (1 composite). The latter includes p=349,q=351,r=3, previous odd label l=17 at t=61423 from Cprev=122484, then even p at n=61424, C=122500=350^2, w=1,d=346,Z=122848. This exercises (5), and shows why (4) needs same-side ancestry. 32 additional abstract twin-pair reset controls in both orientations check forced 3,w=4.

## 8. Exact remaining direct target

Under finitely many twins all sufficiently large minimal opposite-class reset arrivals must be late entries (2), and their same-side predecessor must satisfy (4). To prove infinitely many twins it would suffice to show arbitrarily large actual labels p in this minimal geometry with either early entry (3) or a sufficiently large same-side predecessor. This is a different target from a quiet-ending word or control of a sum: the conclusion is a twin pair inside a selected neighbor, and forced next label 3 means no terminal plateau is needed.

But it remains open to force such geometry and entry at arbitrarily large labels; the exact canonical first-event criterion exposes a genuinely restrictive additional quadratic competition. The composite counterexample prevents replacing the open ancestry/entry condition with an unconditional claim that minimal geometry itself forces twins. Next: explore square/square-minus-two phase-space reachability and the distribution of actual first entrances into these exact horizons, with the late-entry window and previous-label divisibility as a direct exclusion mechanism. No Lean executable available here; no kernel proof or solved conjecture. Main and sibling branches unchanged.
