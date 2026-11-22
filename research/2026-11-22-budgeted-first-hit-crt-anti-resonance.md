# A166944: CRT–first-hit anti-resonance via a budgeted finite gcd wheel

Date: 2026-11-22 JST. **Status:** elementary PAPER theorems, complete exact recurrence / CRT finite tests and a universal finite-state sieve at budget 8. These are NOT a global Cap B proof or twin-prime infinitude proof, and no new Lean compilation was performed.

Inputs: [common-core CRT, permutation-energy and overlap depth](2026-11-22-return-overlap-CRT-energy.md), [first-hit factor clock formula](2026-11-22-terminal-cutoff-factor-short-crossing-dichotomy.md), [terminal F-envelope](2026-11-22-high-growth-terminal-f-envelope.md), and the actual recurrence in [A166944/Lemmas.lean](../A166944/Lemmas.lean).

The crucial advance is a **new, systematic first-hit sieve for a CRT-rigid core**, rather than merely observing that the product of overlapping prime keys is large. It can strictly reject CRT-admissible interior growth candidates, and its small-budget version depends on finitely many modular states, regardless of the magnitude of the actual sequence index.

## 1. Definitions and basic exact lemma

For the original A166944, write D(n)=a(n)-n and d(n)=D(n)-D(n-1)+1. For n>=3, C=D(n-1) is even, and

    d(n) = gcd(n,C-1)            if n even,
           gcd(n-2,C+1)          if n odd.

All d(n) are positive odd integers, and every horizon increment d(n)-1 is even and nonnegative.

Fix u<v and an even nonnegative candidate growth budget h. Put

    Lambda_h = lcm(1,3,5,...,h+1).

Define a **truncated-factor gcd replay** from the exact starting state C=D(u):

    Ctilde(u)=C;
    dtilde_h(n)=gcd(n,Ctilde(n-1)-1,Lambda_h)              for n even;
               gcd(n-2,Ctilde(n-1)+1,Lambda_h)           for n odd;
    Ctilde(n)=Ctilde(n-1)+dtilde_h(n)-1.

**Budgeted finite-wheel soundness theorem (PAPER):**

    boxed: D(v)-D(u)<=h  ==>  for ALL u<=n<=v:
           Ctilde(n)=D(n), dtilde_h(n)=d(n) (n>u).        (1)

Proof by induction. If the actual total growth is <=h, every true increment e=d(n) obeys e-1<=h and hence e<=h+1. Since e is odd, e divides Lambda_h. The true gcd e therefore satisfies gcd(e,Lambda_h)=e. Provided prior horizons agree, the truncated triple gcd is gcd(e,Lambda_h)=e, closing the induction. This includes ALL intervening unit steps.

**Consequences.** For any specified even candidate H<=h, if the truncated replay reports a final growth different from H, the original full first-hit path cannot have growth H. This is a ONE-SIDED exclusion: if the truncated replay yields H, a hidden prime factor >h+1 could still force a larger actual gcd, so the truncated agreement alone is not a proof of a realizable path.

The truncated replay depends only on u modulo 2*Lambda_h, C modulo Lambda_h and the interval length v-u. Thus for fixed h and length, its complete necessary-condition table is FINITE and independent of M, and can be exhaustively checked on one complete residue wheel. The modulus grows quickly with h, however.

## 2. Combining CRT, parity and the first-hit clock

Consider distinct primes p_i>=5 with selected first/second increment-factor uses (u_i,v_i), all first hits preceding all second hits. Put u=max_i u_i < v=min_i v_i. Let H=D(v)-D(u) and

    F_i=[D(u)-D(u_i)]+[D(v_i)-D(v)].

When the EXTERIOR event-growth fringes F_i are part of a specified prospective path, they are known nonnegative sums **outside** (u,v]. This condition is important: without specifying the fringes, CRT does not determine H. With tau_i in {0,-2,+2} chosen from the parity of (u_i,v_i), the exact factor-reuse congruences give

    H == tau_i-F_i (mod p_i).

CRT gives H==h0 mod P, P=prod_i p_i. As H is even and P odd, the parity-corrected progression is

    H == he mod 2P,
    he=h0 if h0 even, else h0+P.                       (2)

The actual horizon restriction gives

    0<=H<=B=2(v-u)+X(u),  X(u)=2u-D(u)>=0.            (3)

**CRT+first-hit floor-lifting lemma (PAPER).** From the known state (u,C), compute the first j exact nonunit first hits at indices <=v, with cumulative growth b_j=sum(e_i-1). Every compatible CRT core must obey

    boxed: H >= he + 2P*max(0,ceil((b_j-he)/(2P))).      (4)

If this right-hand side exceeds B, the specified exterior-fringe/factor-return pattern is IMPOSSIBLE. The hits can be computed directly from all prime factors of C-1 and C+1: for each p|C-1 use its first even multiple after the state, and for each p|C+1 use the first odd r with r-2 divisible by p; take the least candidate and repeat at the updated horizon. This tests true FIRST HITS, not merely final residue matching.

**A very cheap necessary jump condition:** let lambda(C) be the least odd prime divisor of (C-1)(C+1), with C even >=6. If H>0, its first nonunit increment is divisible by some such factor, hence

    boxed: H>=lambda(C)-1.                              (5)

If additionally v-u>=2*lambda(C), then H cannot vanish either (an event must occur by then). In particular, if C is divisible by 210, then lambda(C)>=11 and

    boxed: D(v)-D(u) in {0} union [10,+infty).           (6)

This is a genuine universal **growth spectrum gap**. Thus a CRT-rigid core demanding H in {2,4,6,8} cannot begin at an exactly 210-inert horizon. (6) does NOT say that large overlapping prime factors cannot coexist; their small-prime resonance can still trigger tiny growth, as in the 12-key real example below.

## 3. An ACTUAL 5/11 overlap where first-hit rules eliminate a CRT candidate

The original sequence has the selected factor-return pairs

    p=5:  first event n=60,  D(60)=100; return n=150, D(150)=300.
    p=11: first event n=66,  D(66)=132; return n=343, D(343)=658.

Their common core is (u,v]=(66,150], C=D(66)=132, B=2*(150-66)+X(66)=168. The p-fringes yield

    H==3 mod5, H==3 mod11,
    H==3 mod55 and H==58 mod110 (using EVEN growth).

Consequently, BEFORE first-hit screening the only candidates under B are

    H in {58,168}.

For h=58 the budgeted finite wheel gives total growth **6**, not 58. Therefore H=58 is impossible for any event history beginning at the exact state (66,132).

Even more transparently, the EXACT first-hit clock from (66,132) yields

    n=79:  e=7,   cumulative growth 6;
    n=141: e=139, cumulative growth 144;
    n=150: e=25,  cumulative growth 168.

After the first TWO forced hits, (4) upgrades the lower bound to H>=168, which together with B=168 fixes H=168. This is a genuine nontrivial example in which CRT arithmetic by itself leaves a false candidate and **first-hit minimality removes it**. (A third key p=13 would also make the CRT rigid in this particular actual history, but the 5/11 certificate uses only two.)

## 4. Budget-8 universal 630-by-315 modular sieve

For h=8,

    Lambda_8=lcm(1,3,5,7,9)=315.

The finite-wheel replay is periodic in the initial index u modulo 630 and in the even initial horizon C modulo 630 (315 possibilities). Therefore there are exactly 630*315=198,450 residue states, INDEPENDENT of the magnitude of u,C.

For an interval of length exactly 10 indices, the COMPLETE exhaustive truncated-gcd census is:

    truncated growth 0:   31,590 classes
    truncated growth 2:   30,664 classes
    truncated growth 4:   38,873 classes
    truncated growth 6:   26,156 classes
    truncated growth 8:   21,763 classes
    truncated growth >8:  49,404 classes
    total:                198,450 classes.

Thus ANY actual interval of length10 with true growth H=8 must have one of the 21,763 residue pairs surviving this sieve (not all surviving pairs imply an actual path). In all 630*3 states with C==0 mod210, the truncated growth is zero. So a core with C==0 mod210 and H=8 is universally impossible, for ANY length.

By contrast, the genuine 12-key overlapping return core (u,v]=(356873,356883] starts at C=713458==88 mod210 and has two actual first hits

    (356874,3), (356883,7),

giving exactly H=2+6=8. Its budget-8 wheel reproduces both hits. This demonstrates the precise SMALL-FACTOR RESONANCE that permits enormous prime-return overlap without an immediate contradiction.

## 5. A global clock-exhaustion / terminal-roughness theorem for any small growth interval

Let h be even, H=D(v)-D(u)<=h and Q=Lambda_h. A state t is **h-rough** when neither D(t)-1 nor D(t)+1 has a prime factor <=h+1, equivalently

    gcd(D(t)-1,Q)=gcd(D(t)+1,Q)=1.

**Small-prime clock lemma:** if state t is not h-rough, an odd prime q<=h+1 divides D(t)±1. If the horizon stays fixed, its corresponding parity-gcd hit occurs within 2q<=2(h+1) indices. If any event happens earlier, that also counts. Thus the NEXT actual nonunit hit occurs within 2(h+1), whenever that time lies in the interval.

**Terminal-roughness theorem (PAPER).** If

    v-u >= (h+2)*(h+1),       H<=h,                 (7)

then there exists t in [u,u+h*(h+1)] such that t is h-rough AND

    d(n)=1 for all t<n<=v.                            (8)

In particular, the last nonunit hit within (u,v] occurs no later than u+h*(h+1), and the terminal quiet suffix is at least (v-u)-h*(h+1).

Proof. At most h/2 nonunit hits can occur under growth budget h, since each has growth>=2. As long as the current state is not h-rough, the next hit occurs within 2(h+1) indices. If every state through u+h(h+1) remained non-rough, (7) would force h/2+1 hits before v, giving growth>h. Hence an h-rough state appears by u+h(h+1). At such a state all prime factors of both horizon neighbors exceed h+1. Any next nonunit hit, with horizon still fixed, would have e>h+1 and growth>h, contradicting total budget. Hence all later increments up to v are 1. QED.

At h=8: ANY actual growth-at-most-8 interval of length >=90 has, by index u+72, an 8-rough state and subsequently only unit increments. This is an exact *bounded-growth => early terminal quiet* result. For global Cap B this applies only when some sufficiently long subinterval has independently established small growth; it does not itself bound the canonical G_M or force bad terminal crossings away.

## 6. A new LOCAL low-growth criterion sufficient for Cap B

Let M>=23 be a genuinely attained canonical record, s0=M+2, K=floor((7M-1)/4), and put t=isqrt(D(K)+1). Choose any u in [s0,K] and an even h>=0 with

    D(K)-D(u) <= h.

If the terminal subwindow length L=K-u satisfies BOTH

    L >= (h+2)*(h+1),
    L >= h*(h+1)+2*t+8,                            (9)

then D(K)-1 and D(K)+1 are twin primes, and Cap B holds at that record.

**Proof.** The terminal-roughness theorem on [u,K] gives a rough state r<=u+h(h+1) after which all increments up to K are 1. Hence D(r)=D(K) and

    K-r >= L-h(h+1) >= 2*t+8.

The already kernel-checked AllIndices.twins_of_slow_interval applies to [r,K]: D(K)>=4, and

    9*(D(K)-D(r))+32+8*t = 32+8*t <=4*(K-r).

It concludes that D(K)-1,D(K)+1 are prime. The previously checked CapSampleExact.cap_iff_twins_at_cutoff then yields Cap B for genuinely attained sufficiently large records (its Lean statement has M>=968); for smaller M the twin conclusion stands independently and any Cap B use should match its own hypotheses.

For **h=8**, (9) becomes the concrete, simple condition

    boxed: D(K)-D(u)<=8 and K-u>=max(90, 80+2*isqrt(D(K)+1))
          ==> D(K)-1,D(K)+1 prime.                  (10)

This criterion is **LOCAL**: it does not constrain the accumulated growth before u. In principle it can be certified using the CRT first-hit wheel on a terminal core; the missing *global* assertion is the existence of such an adequately long low-growth terminal subwindow on unbounded genuinely attained canonical records. A bounded h is a strong hypothesis; this is not a proof of Cap B for all records.

## 7. Independent audits and the remaining precise gap

Companion [first_hit_budgeted_crt_audit.py](first_hit_budgeted_crt_audit.py) computes the original A166944 through n=2,500,000 (250 nonunit hits including n=2) and all 125 consecutive large-prime reuse intervals p>=5. Their intersections give **968** distinct selected TWO-key overlapping-return configurations.

Among these 968, 334 have CRT product P greater than the intrinsic local horizon cap B, so CRT alone fixes H. The other configurations may have several arithmetic candidates.

For a reproducible restricted sample, enumerate every parity-compatible CRT candidate H<=128 that is also <=B and whose overlapping core length v-u<=2000. This yields **522** candidate assignments (some are deliberately FALSE alternatives to the actual H), of which the budgeted finite wheel rejects **136** and leaves **386** not rejected. The retained candidates are necessary-only survivors, not claims of realizable paths.

The actual direct-gcd trace also passed the wheel identity on 23,261 bounded-growth sampled subintervals (H<=8), and the terminal-roughness theorem was checked on 31,204 sampled windows of length90/150/230. The universal 198,450-state 8-budget table is exhaustively enumerated, not sampled.

**Open:** These finite-wheel/CRT anti-resonance certificates only exclude specified short-growth possibilities with a known starting horizon and sufficient knowledge of the outer fringe event growth. A generic genuinely attained canonical failure could have growth h scaling with M, and Lambda_h grows exponentially in h. No theorem forces a large set of incompatible low-budget CRT cores along every putative bad path. The event-history/fringe correlation needed for Cap B is still absent. No new Lean kernel compilation and no proof of twin-prime infinitude.
