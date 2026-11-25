# Descending relay resonance: cubic gap obstruction

Continuation of [9231f33](https://github.com/tara-sooo/A166944-Lean/commit/9231f33738b739c761f1bfd4c58df24782f7656a), branch `research/min-direct-arithmetic-2026-11-25`. Paper deductions and exact bounded computations; not Lean verified. Twin infinitude and A166944 remain open. GitHub write attempts failed; this local copy and its audit are the recoverable artifacts, not a verified remote commit.

## 1. Hypotheses

Actual adaptive MIN chooses the earliest eligible future tick, ties by least odd prime, with p² ≤ H+1. At an event of sign e=+1 (even) or −1 (odd), H=pq+e, post-horizon Z=H+p−1, adjusted deficit D=2n−Z−6I, I=(1−e)/2. Consider four successive nonunit events p,a,b,p with a,b different from p and from 3, both endpoint waits >6, minimal return q2=q1+2, even→odd, D1=D2=0. Assume p≥101 and p³>64(Y+1), all pre-horizons ≤Y, and Q=q2 composite. The previous note proves p≡7 mod12, a,b≡1 mod3, a+b=p+1, c=a−b>0, D_b=2b, w2=(c+4−6I_b)/2, and c≤4r<p/2, where r=minfac(Q)≤√Q. Also Q≥p+2 and Q<p²/64. This note concerns precisely that remaining branch, not arbitrary returns.

## 2. Cubic gap obstruction

First pre-horizon H1=p(Q−2)+1, first post-horizon Z1=p(Q−1), last pre-horizon H2=pQ−1. The even reset implies Q≡1 mod4, and H2≡0 mod3 gives Q≡1 mod3, hence Q≡1 mod12.

The two relay pre-horizons are Z1 and Z1+a−1=pQ−b. With signs e_a,e_b in {−1,+1}, their divisibility conditions are

    (c+1)(Q−1) ≡ −e_a mod a,
    (c−1)Q ≡ e_b mod b.

Define positive integers u=((c+1)(Q−1)+e_a)/a and v=((c−1)Q−e_b)/b. The relay cofactors are respectively 2(Q−1)−u and 2Q−1+v, both odd. Therefore u is odd and v even. Eliminating Q gives

    K=(c−1)u−(c+1)v,
    bK+c(c−1)u=−(c²−1)+(c−1)e_a+(c+1)e_b=C.

Since c is a positive multiple of 6, C<0 and K is a negative odd integer. Thus b≤c(c−1)u−C. Since u<(c+1)Q/a and −C≤c²−1+2c,

    ab < c(c²−1)Q+a(c²+2c−1) < (11/9)c³Q.

The last step uses a<Q and (c+2)/c²≤2/9 for c≥6. Hence c³>9ab/(11Q). In fact K≡1+e_b−e_a mod3, so |K|≥5 if the relay sides agree, ≥3 if e_a=−1,e_b=+1, and ≥1 otherwise. Writing k0 for these values, the strengthened bound is c³>9k0 ab/(11Q).

Because c<p/2, ab=((p+1)²−c²)/4>3p²/16. Combining c≤4r gives

    r³Q > 27k0 p²/11264.

Thus if Q=o(p²), bounded least factor r is impossible. In balanced range Q≤A p with fixed A, c=Ω_A(p^(1/3)), r=Ω_A(p^(1/3)), and c=O_A(√p). In this range Q can have at most three prime factors counting multiplicity for sufficiently large p: four factors would give r⁴≤Q, incompatible with the cubic lower bound as p grows. These are necessary inequalities, not a full exclusion. The narrow descending resonance cannot have a fixed difference c when Q=o(p²).

## 3. Stronger scale: both relay cofactors prime

If p³>4096(Y+1), then r<p/64, c<p/16, a>p/2, b>15p/32. From the previous reset lemma D_a=0 or 2a (D_a=0 iff a≡1 mod4 because Z1≡0 mod4). Exact waits are

    w_a=(a−1+D_a+6I_a)/2,
    w_b=(3b−1+6I_b−D_a−6I_a)/2,
    w2=(c+4−6I_b)/2.

Their sum p+2 equals the endpoint clock difference. Thus w_a>(p−2)/4 and w_b>11p/64−13/4. Each relay cofactor is ≤(Y+1)/min(a,b)<p²/1920. For p≥101 both waits exceed twice the square root of their own cofactor, hence both relay cofactors must be prime by the first-hit roughness lemma: if a cofactor were composite, its least prime factor would be strictly smaller than the chosen label and would hit earlier. This does not certify Q prime. The branch then requires prime relay cofactors as well as a rough composite final cofactor.

## 4. Exact finite decision per p,a,b

Since a,b are distinct primes, either c+1 or c−1 is noninvertible modulo the corresponding prime, making the sign congruence impossible, or CRT fixes a unique Q residue mod ab for each of four sign pairs. As ab>3p²/16 and Q<p²/64, there is at most one possible Q, its least nonnegative representative. Check Q≥p+2, Q≡1 mod12, composite with r=minfac(Q), w2>6, w2<2r, c≤4r; check exact relay waits within [1,2a] and [1,2b]. From (t,H)=(p(Q−1)/2,p(Q−1)) the actual three events a,b,p must occur with the prescribed signs and waits. This is an exact necessary test without testing ancestry or the first p event. Existence of the full abstract four-event segment with first wait>6 is equivalent to additionally checking the first p event at n1 from start (n1−7,H1), since any longer valid wait can be shortened to seven without changing its winner and the envelope holds for p≥101. Canonical ancestry is a separate question.

## 5. Bounded diagnostics and reproducibility

Run `node min_direct_relay_gap_audit.mjs 50000` from this file's directory. The final local source was executed with Node v22.16.0, output in `min_direct_relay_gap_results.json`. The earlier ECMAScript execution gave the same primary counts. All assertions passed in the final run. Only P≤50000 is supported by this implementation's Number intermediates; exact cancellation and bound products use BigInt. Initial floating-point cancellation in bK+c(c−1)u=C produced a one-unit error at p44563,c21930; the final version uses BigInt for this equality and the cubic inequalities. Nonpositive or out-of-period waits are rejected as impossible candidates rather than asserted possible.

Through P=50000, enumerate primes p≡7 mod12, all prime b with (p+1)/4<b<(p+1)/2, a=p+1−b also prime, both ≡1 mod3, and all four relay sign pairs. Results:

- 126,429 prime relay pairs; 505,716 CRT candidates; 2,868 satisfying Q≥p+2, Q<p²/64 and Q≡1 mod12. All satisfy the exact elimination identity and sign-strengthened cubic gap inequality.
- 2,861 have last wait>6; 87 composite Q with w2<2r and c≤4r, including 18 with Q−2 prime. Five fail relay wait ranges; remaining 82 are tested by actual first-hit clocks. 35 pass the independent initial p hit at n1 from n1−7. Eight match the first relay a from the reset; none matches the second relay b, and thus none matches the full pattern. All 90 independent literal parity-GCD next-event checks match event-jump implementation.
- No candidates satisfy the stricter 4096 scale; relay-cofactor primality there is a paper deduction, not a positive empirical instance.

Example p12163,a6091,b6073,c18,Q1240321, minfac(Q)=23, e_a=−1,e_b=+1, w2=11, Q−2 prime. First p can hit from n1−7. First relay would wait9139, but actual 11 wins in19 ticks. Example p4099,a2083,b2017,c66,Q212809,e_a=e_b=−1,w2=32: first relay2083 wins at3127 ticks, but5 wins four ticks later instead of2017 (prescribed wait942). Neither example establishes the full target pattern.

## 6. Status

Under finite twins and the previous hypotheses with Q−2 certified prime, the only surviving non3 even→odd minimal two-relay reset case now has both an upper and a lower bound on c and r, plus two prime relay cofactors at stronger scale. The CRT search reduces all possible Q at fixed p and relays to a single integer per sign pair. The remaining missing result is an unbounded exclusion or a global forcing theorem for the specified returns. This is not a contradiction with finite twins. No Lean/lake executable or kernel verification; no external novelty claim. The independent branch was read but remote write and readback did not succeed in this turn; no new remote commit is claimed.
