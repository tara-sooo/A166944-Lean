# Exact inverse MIN and square-entry obstructions

Continuation of [4816c99](https://github.com/tara-sooo/A166944-Lean/commit/4816c997be58257edf27db68badb8124ca2859b8) and the intervening [near-square refinement 910684f](https://github.com/tara-sooo/A166944-Lean/commit/910684faf4ae458aa30403554fd8f8989ab4e443), on the same independent branch. The latter correctly notes that every odd prime factor of (p+1)^2+1 is 1 mod4, so the earlier putative both-3-mod4 semiprime alternative in the tight first-event criterion is vacuous. Here the focus is actual canonical reachability, not only first events. Paper proofs and finite exact diagnostics, not Lean kernel-checked; no external novelty claim or proof of twin infinitude. No cumulative cost, merger, moment, or probabilistic assumption.

## 1. The entire odd minimal orientation is unreachable

Use the adaptive MIN as before. A canonical root is (t,C)=(M+2,2M-2), M odd >=5. At an event n>t, selected label p is an odd prime <=sqrt(C+1), dividing n and C-1 if n even, or n-2 and C+1 if n odd. The poststate is (n,Z=C+p-1). In particular an event ending at (t,H) has label l dividing both t and H for t even, or both t-2 and H+2 for t odd. Actual plateau starts are roots or post-event states; a quiet tick is not a new plateau start. The envelope H<=2t holds.

Let p>=7, p=3 mod4, x=p+1, and consider the odd minimal candidate

    C=x^2-2, Z=p(p+3)-2, n=p(p+3)/2+2, delta=2n-Z=6.

Write w=n-t for the plateau wait. If p=1 mod3, p+2 is divisible by 3 and the previous same-side 3 hit is n-2, so w<=2 (section 2 of 4816c99). If w=1 the previous event must be even, hence l | C and n-1. Since 2(n-1)=x^2+x, l divides x+2 and x^2-2, thus l|2, impossible. If w=2 the previous event must be odd, hence l|C+2=x^2 and n-4. Since 2(n-4)=x^2+x-6, l divides x and 6, hence l=3, but x=2 mod3. Impossible.

If p=2 mod3, x=0 mod3, so C-1=x^2-3 is divisible by 3, and n-1 is even divisible by 3. This is an eligible opposite-side hit, hence w<=1. The same w=1 argument excludes an incoming event. These cases cover all prime p>=7. No canonical root has C=2 mod4, while x=0 mod4 here. Thus no actual canonical trajectory has the odd minimal arrival at any p>=7, independently of finite twins and even when p+2 is prime. The prior abstract odd-side clock/cofactor implications remain valid in the relaxed state space; the odd side is not an available canonical twin-witness target. The even-side target remains meaningful.

## 2. Exact local incoming gates for even orientation with small composite cofactor

Let p=1 mod4, x=p+1, C=x^2, Z=p(p+3), n=Z/2, and r=minfac(p+2)<p. Then w<=r-1 by the sharp backward-clock gate in 4816c99. A preceding even event at t=n-w has label l|x and l|w+1, w even. A preceding odd event has l|x^2+2 and l|x-2w-8, w odd, so l| (2w+8)^2+2.

### r=3

Here p=1 mod12, x=2 mod3, p>=13, w<=2. The root phase t=C/2+3 would have w=(p-7)/2>=3 and is excluded. At w=2, l|x and l|3, impossible. At w=1, l|102=2*3*17, x=10 mod l. The mod3 condition rules out 3. Hence l=17, p=9 mod17. Combining with p=1 mod12 gives exactly

    p=145 mod204.

For such a prime p, this is also sufficient for a LOCAL two-event chain starting at the valid abstract state (n-2,C-16): at n-1 the raw plus gcd has odd prime factors only 17, since the two arguments force l|x+7 and x^2-15, hence l|34; it contains 17. At n the raw minus gcd is exactly p, since gcd((p+3)/2,p+2)=1. Both labels are in the adaptive pool (the first prime in this class is 349). No claim of canonical reachability of this abstract start. All actual canonical minimal arrivals with r=3 must obey the displayed congruence. In particular Dirichlet gives infinitely many prime p=1 mod12 not 145 mod204, e.g. p=1 mod204, that cannot give the desired event from ANY canonical root.

### r=5

Here p=53 mod60, x=0 mod3, x=-1 mod5, p>=53, w<=4 and the canonical root phase is too early. For w=4 the required even l=5 cannot divide x. For w=2 the required even l=3 is valid as a local arrival: at t=n-2 from C-2 the eligible minus 3 clock wins. The only intervening tick before n is n-1 odd; a competing factor divides gcd(n-3,x^2+1), hence divides 82 and is 41 exactly when x=9 mod41. This is eligible since p>=53. Thus the w=2 chain exists iff p != 8 mod41.

At w=1 the odd predecessor must be 17 (3 does not divide x^2+2) and p=9 mod17, and the same one-tick 17 construction works. At w=3 the odd predecessor divides 198=2*3^2*11; 3 does not divide x^2+2, leaving 11. But at its proposed arrival t=n-3 from C-10, the plus neighbor x^2-9 is divisible by 3, and t-2=n-5 is divisible by 3 (n=2 mod3). The smaller label wins the tie. So w=3 is impossible.

The exact local two-event gate is therefore

    (p != 8 mod41) OR (p = 9 mod17).

This equivalence concerns existence of a valid abstract predecessor chain, not existence of a canonical root. An actual canonical minimal arrival must satisfy it. Example p=19073 is blocked at both options; p=14153 satisfies the second option despite p=8 mod41 and can have the local 17 predecessor.

## 3. Complete inverse algorithm with a finite interval per incoming label

For a candidate post-event state (n,Z), fix side by parity of n. Any incoming label p is an odd prime divisor of

    gcd(n,Z)          (n even),
    gcd(n-2,Z+2)      (n odd).

Set the unique predecessor horizon C=Z-p+1. Reject C<8 (canonical roots start at 8), p^2>C+1, or any p that is not the least prime factor of the corresponding raw GCD at n with that C. Because p itself is eligible, every smaller raw GCD factor would also be eligible, so this exactly tests arrival/tie competition.

For every eligible clock q on C, let b_q=0 if q|C-1 or b_q=q+2 if q|C+1. Let lag_q be the least POSITIVE residue of n-b_q modulo 2q (zero represented by 2q). It is the distance from n to the last strictly earlier hit. Put L=min lag_q. Then the exact interval of predecessor plateau-start times is

    max(C/2,n-L) <= t <= n-1.                       (I)

Indeed a strictly earlier eligible hit in (t,n) would defeat p. Every earlier eligible hit is at or before n-L, so the whole interval suffices as well. The start-time envelope C<=2t is included. The interval does NOT assert that (t,C) is reachable from a root; that is tested recursively.

For each admissible predecessor (t,C), it is a canonical root iff C=0 mod4 and t=C/2+3 (M=C/2+1). Otherwise it must be an earlier post-event state with another inverse edge. Even when the node is a root, continue exploring its incoming edges if collecting ALL possible roots rather than only one witness. Both time and horizon strictly decrease on inverse edges; the graph below a specified target is finite. Memoization/visited sets can deduplicate exact (t,C) nodes. This gives a complete decision procedure for whether a specified finite target event occurs from any canonical root, and can enumerate every possible root. No fixed horizon window, max-event truncation, or source-density approximation is needed, provided the actual inverse traversal completes. A computational budget hit must be reported as unknown, not unreachable.

This inverse algorithm is for the specified adaptive model; for a fixed B the clock pool and eligibility test must be changed accordingly. Its completeness is not an asymptotic argument forcing unbounded targets to be reachable.

## 4. Resultant bound and the exact escape from bounded reverse ancestry

For the even target n=(x^2+x-2)/2, parametrize an earlier candidate post-event node as (n-A,H=x^2-D), A>=1, D>=0 even. For its incoming label l define

    K=2A-D+2   if the node time is even,
    K=2A-D+8   if the node time is odd,
    R=K^2-D    if even,
    R=K^2-D+2  if odd.

The arrival divisibilities imply l | x-K and l | R. Proof: subtract H or H+2 from twice the clock argument, then substitute x=K mod l. The analogous formulas for odd targets replace +2,+8 by -2,+4, although section 1 rules out canonical minimal odd events.

If R!=0, l<=|R|, a bound depending only on the relative offsets, not x. A reverse edge increases D by l-1 and A by a wait at most 2l. For even targets with fixed r, initial A<=r-1,D=0. Writing S=A+D+8, |K|<=2S and |R|<=5S^2; each nonzero-resultant reverse step gives S_new<=16 S^2. A root requires x=8+2A-D<=2S. Therefore for fixed r and a fixed inverse depth k, a sufficiently large x cannot have a canonical root within those k earlier events unless at least one zero resultant occurs. E.g. a sufficient bound for an all-nonzero path of at most k earlier events is x<= (16(r+7))^(2^k)/8. This is a finite-depth structural statement, not a bound on the total depth of actual trajectories.

If R=0, H or H+2 factors as (x-K)(x+K). Since H>=8, |K|<x. K,x even, so l is an odd prime factor of the positive even x-K and l<=(x-K)/2. This is a scale-dependent bound, and l need NOT be bounded in terms of fixed r,k alone. Calling the R=0 situation a resonance here is just terminology for exact vanishing of the integer resultant, not a probabilistic phenomenon.

## 5. Unbounded earlier labels really can enter the small-r local gate

A zero resultant is not merely a formal exception. Fix ANY odd prime l>17. We construct arbitrarily large prime p with p+2 divisible by 3 and an actual four-event chain from a valid ABSTRACT plateau start:

    start at n-8: x^2-l-17
    n-7: label l,  post x^2-18
    n-2: label 3,  post x^2-16
    n-1: label 17, post x^2
    n:   label p,  post p(p+3).

Here x=p+1, n=p(p+3)/2, and impose

    p=145 mod204, p=3 mod l,
    x != -9 mod31,
    x != -5 mod r' for each odd prime r' dividing l-9.

These conditions can be combined into a reduced arithmetic progression for p: the first two moduli are coprime since l>17 (except l=17 excluded); p=3 mod l is reduced. No odd r' dividing l-9 is 3 or l; if r'=17 the fixed x=10 mod17 avoids -5. For any other odd r', choose x avoiding 1 and -5 (and -9 if r'=31). If l=31, x=4 mod31 already avoids -9, and otherwise the mod31 requirement has a reduced choice. Thus CRT gives a reduced class and Dirichlet supplies arbitrarily large prime p. Take p>l+2 to ensure all cutoffs and positive horizons. This is one prime variable after l is fixed, not simultaneous primality in two linear forms.

At n-7 odd, the clock argument satisfies 2(n-9)=(x+5)(x-4). The pre-event plus neighbor is x^2-l-16. The label l divides both by x=4 mod l. Any other prime divisor of the raw gcd either has x=4 mod r' and then divides l, impossible, or has x=-5 mod r' and divides l-9, excluded by construction. Thus l wins at this first tick. The resulting node H=x^2-18,A=7 is odd, with K=4,R=0; its incoming label is unbounded as l ranges over primes.

At the next four ticks n-6,n-5,n-4,n-3 with H fixed, the possible raw odd prime gcd divisors divide respectively 6,-16,62,8 by eliminating x. The candidate 3 at n-6 is absent since x=2 mod3; the candidate 31 at n-4 is excluded by x!=-9 mod31; the other two integers have no odd prime factor. At n-2 the minus 3-clock wins (n-2=0 mod3 and H-1=x^2-19=0 mod3). The remaining one-tick 17,p arrivals are exactly section 2. The starting state satisfies the envelope, but is not asserted to be a canonical root or reachable from one. Its deficit is of order p; this is precisely what remains uncontrolled.

Thus even r=3 and the forced last labels 17,p do not imply a uniformly bounded sequence of earlier labels: just three previous events suffice to admit an arbitrarily large label in a valid local trajectory. This disproves the proposed blanket finite-depth bounded-ancestry strategy in the abstract phase space. It does not disprove a global canonical reachability exclusion. It also explains why treating R=0 as a negligible exception would be incorrect.

## 6. Reproducible exact diagnostics

[Inverse audit at f1cdf0f](https://github.com/tara-sooo/A166944-Lean/blob/f1cdf0fff7ab33ad220e636d0cde35eeaa79ca55/research/min_direct_square_inverse_audit.mjs), blob 8332e557e2f8a76861e3c7160d1949ee1e4cb275; [resonance construction at ba4807e](https://github.com/tara-sooo/A166944-Lean/blob/ba4807e92c50cb3d4fc0eebc6e8501e204532c21/research/min_direct_square_resonance_audit.mjs), blob 5dfcd7121b99e8efbb800aa08d122e1b8ef26f2c. Exact remote readback for both. Run from repo root:

    node research/min_direct_square_inverse_audit.mjs 2000 500000
    node research/min_direct_square_resonance_audit.mjs

Executed the actual ECMAScript functions in the tool runtime, not a separate Node process. Exact inverse interval compared with direct next-event computation at 138832 target/start pairs. Complete inverse graph traversal for all 300 prime labels 7..2000 (154 odd-orientation targets, all excluded). 70660 visited predecessor nodes total, largest single graph 24753, zero budget failures. 294 targets unreachable from ANY canonical odd root, 6 reachable. 13393 incoming-resultant tests, including 14 zero resultants; all passed. A separate complete forward traversal of 2426 roots for the smaller range p<=97 (25973 events) matched all 22 reverse root sets exactly. Each displayed successful witness was replayed through the actual forward first-hit rule.

| label p | q=p+2 prime? | all canonical roots | prime canonical roots | example M |
|---:|:---:|---:|---:|---:|
|17|yes|1|0|161|
|149|yes|2|1|11251|
|269|yes|4|1|36451|
|317|no (11*29)|11|4|50387|
|569|yes|24|5|162451|
|1289|yes|47|9|831917|

The 11 roots reaching p317 are 50327,50329,50331,50333,50335,50337,50339,50341,50381,50387,50389. The prime ones are 50329,50333,50341,50387. This extends the previous bounded trajectory scan to exact all-root coverage. No r=3 even composite target is reachable in this finite range: only p349,757,1777 have local incoming gates; exhaustive recursion excludes each. No r=5 target is reachable either. These are finite facts, not global exclusions.

Additional independent small-window local tests up to p=20000: 555 even r=3 cases, 32 with local gate; 141 even r=5 cases, 140 with local gate (p19073 blocked; p14153 rescued by label17). All agree with exact formulas. The separate BigInt construction checks four-event chains with l=19,173,1009,10007,100003 and p=3613,349,1802077,22956061,167805037 respectively. All primes and exact ticks checked, no Number rounding for the large cases. These are deliberately abstract starts, not root witnesses.

## 7. Remaining proof problem and route selection

Odd minimal geometry is now eliminated from the canonical proof target, independent of finite twins. Even minimal geometry is sparse in the complete finite inverse test and often forbidden by local modular structure. Under finitely many twins, any sufficiently large reachable even minimal target has composite p+2 and a constrained late entry. The inverse interval method is exact and avoids finite prefix sampling bias. But the local resonance construction demonstrates that repeatedly bounding earlier labels by offset-only constants cannot succeed without treating the zero-resultant case and the root phase.

A next genuinely global target is to control canonical inverse reachability through these resonant branches, or to find a different arithmetic geometry whose occurrences can be forced by the infinite trajectories implied by finite twins. Proving infinitely many reachable minimal even targets with prime cofactor remains open; even existence of infinitely many reachable minimal targets of either cofactor type is not proved. No Lean executable was available, no Lean files changed; no external novelty claim. Main and other branches unchanged.
