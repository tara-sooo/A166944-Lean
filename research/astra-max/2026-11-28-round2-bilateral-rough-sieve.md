# A two-sided lower sieve for distinct first-height sites

Issue #10, 2026-11-28 JST. Starting head eb72059ee1a8704e52f7a0fba1fccc1011d31b66. This paper argument changes the source ensemble: all rough odd neighbors are admitted, and both directions of the shift have usable prime-product factorizations. The count has multiplicity one per center. It is not a lower for the prescribed .374900–.374950 prime-factor box in the second brief.

## Theorem

Let \(L=\log R,\ \Pi_R=2C_2R/L^2,\ C_2=\prod_{\ell>2}(1-1/(\ell-1)^2)\). In every sufficiently large slab, at least \(0.01\Pi_R\) distinct canonical centers have **both** neighbors free of primes below \(4R^{.324}\). They attain \(H=\lfloor R^{.324}\rfloor\) for the first time at their original position, with zero gain. The constant 4 can be replaced by any fixed positive multiplier in the arithmetic claim. The proof uses the classical \(4/7\) distribution theorem for weighted products of primes, independently of Pascadi's unit-factor endpoint.

## Exchange the two neighbors

Use odd \(n=A-1\) in \([R-1,2R-1]\), with right neighbor \(m=n+2\). Let \(C\) indicate least prime factor at least \(4R^c\), \(E\) indicate least prime factor at least \(R^a\) but below \(4R^c\), and \(U=C+E\), with \(c=.324,\ a=.207\). Thresholds apply equally at both ends of the directed pair. At each integer one has exactly
\[
 C(n)C(m)=C(n)U(m)-C(n)E(m).
\]
For the first term enumerate \(n\in C\) by its full list of ordered prime factors, and lower-sieve \(n+2\). For the second term enumerate **\(m\in E\)** by its full list of prime factors and upper-sieve \(m-2\). Primes themselves form a one-factor sector. A product is counted once through its ordered factors; repeated large primes contribute \(O(R^{1-a}+R^{1/2})\) by the square-divisor bound. Translations of slab endpoints by bounded amounts contribute \(O(1)\).

Put \(d=4/7-1/10000\). For a fixed polynomial roughness cutoff \(z\) the linear sieve has local density \(1/(\ell-1)\) at odd primes and \(V(z)\sim 2C_2e^{-\gamma}/\log z\). The product-sequence row of unsifted size \(J R/L\) thus contributes at least \((J\,2\log(d/a-1)/d-o(1)-O(\eta))\Pi_R\) for the first sum. For the second the upper is \((J\,2/d+o(1)+O(\eta))\Pi_R\). Indeed \(2<d/a<4,\ 1<d/c<3\). The fixed sieve approximation parameter \(\eta\) can be taken arbitrarily small before \(R\) tends to infinity. For the upper bound use the smaller cutoff \(\min(4R^c,R^{d/2.1})\), by monotonicity. Its sieve parameter lies in \([2.1,3)\); this respects the printed hypothesis \(z\le Q^{1/2}\) in Wu Lemma 2.2 and gives the identical \(2/d\) coefficient. These are inequalities for the exact shifted populations. No independence assumption or evaluation of a prime-quotient probability enters.

Write \(M(t)=\omega(1/t)/t\), the coefficient of \(R/L\) in the count of \(R^t\)-rough numbers in the slab. It is unchanged by a fixed multiplier at the cutoff. Wu Lemma 2.10 gives this slab formula by subtraction at the two endpoints and continuity of Buchstab's function. Thus the resulting lower coefficient is
\[
 K={2\over d}\left[(1+\log(d/a-1))M(c)-M(a)\right].
\]
The positive term uses the unsifted mass of the entire target-side population. In the subtracted term the mass is only \(M(a)-M(c)\). Replacing the target side by a narrow two-prime box discards this feature.

For an elementary numerical lower use
\[
 M(c)\ge 1+\log((1-c)/c),\qquad M(a)\le .561522/a .
\]
The first counts primes and semiprimes with ordered smaller factor of exponent \(t\in[c,1/2]\) by the prime number theorem and the integral \(dt/[t(1-t)]\). The second is Wu Lemma 2.10 since \(1/a>3.5\). The resulting \(K>0.0136\) leaves room for \(0.01\) in the theorem.

## Distribution and localization details

Wu, *Chen's double sieve, Goldbach's conjecture and the twin prime problem*, Acta Arith. 114 (2004), Lemma 2.2 (pp. 219–220), Lemmas 2.7, 2.9, 2.10 (p. 223), supplies the linear sieve, the fixed residues \(\pm2\), the well-factorable level \(4/7-\epsilon\) and Buchstab's function. In Lemma 2.9 each prime is restricted to a dyadic interval, the product of the lower endpoints is \(X\), and every factor exponent is bounded below. For completeness, the following localization shows why short log-relative boxes are legitimate here.

Cover each ordered product sector by boxes of ratio \(1+L^{-B}\) with fixed sufficiently large \(B\). There are polynomially many in \(L\) since the number of primes is at most four at these cutoffs. Use inner boxes for a lower and outer boxes for an upper. Errors in the bare main masses are \(o(R/L)\): the prime number theorem uniformly on these log-relative intervals, followed by partial summation, gives the bounded-density simplex integrals on compact exponent ranges bounded away from zero. The product-slab face can alternatively be bounded by counting all integers in boundary strips of width \(O(RL^{-B})\), with bounded tuple multiplicity; near-tied factor bins have vanishing exponent volume. Exact prime powers and shared endpoints can be assigned once.

A short prime interval \((U,V]\) is a signed sum of the dyadic intervals \((V/2^{j+1},V/2^j]\) minus the analogous intervals at \(U\), plus a tail below \(2R^{-\kappa}V\). Truncate at \(j=\lfloor\kappa\log_2 R\rfloor\), with a fixed \(\kappa>0\) small relative to the distribution slack. Expand for all variables. Each full dyadic term uses \(X\gg R^{1-4\kappa}\), all factor exponents stay bounded below, and \(D=R^d\le X^{4/7-\epsilon'}\) for fixed \(\epsilon'>0\) on choosing \(\kappa\) small. A well-factorable sequence of level \(D\) is also well-factorable at any larger level, by shrinking each prescribed factor support to a split of \(D\). Polynomially many boxes and signed terms are paid for by arbitrary log savings. Terms with a small endpoint tail have \(O(R^{1-\kappa}L^{O(1)})\) tuples, even counting unrestricted integer entries. Their summed congruence contributions are \(O(R^{1-\kappa+o(1)})\) by the ordinary divisor bound on the nonzero product shifted by 2; the coprime main terms cost only another logarithm. For the single prime row use Lemma 2.7 by subtraction directly. In particular the distribution theorem is never evaluated above the available power level on a telescoping term.

Use the usual Iwaniec weights for the indicated sifting primes. In the box realization of Lichtman §5.1, (5.15)–(5.20), the interval restriction to primes below the cutoff restricts each individual prime variable. The small-prime sieve component is already squarefree. The possible diagonals of repeated rough prime variables can be dropped at an error \(O(R^{1-\xi+o(1)})\) for fixed sieve parameter, since each such repeated prime \(\ell\ge R^\xi\), and summing the trivial progression/main bounds \(\ll R^{1+o(1)}/d\) over \(d\le D,\ \ell^2\mid d\) gives that bound. Use the ordinary factorable components constructed for this sifting set. Finally replacing the coprime reference in the product theorem by the unsifted box count divided by \(\phi(d)\) costs \(\ll B_{\rm box}L R^{-a+o(1)}\): for each original tuple sum \(1/\phi(d)\) over squarefree sieve divisors containing one of its at most four prime factors. This correction is taken for the original boxes.

## From the count to the trajectory

For large \(R\), two \(4R^{.324}\)-rough odd neighbors force \(6\mid A\). At the birth \(h=3\), a possible label through the required age is bounded by \(2H+1\) (also follows from the more generous \(2H+7\)). The verified firstHeightSite_of_rough_birth lemma gives the first hit at age \(H-3\), site \(A\), budget zero. At \(T=\lfloor R^{.324}\rfloor\), all factors also exceed \(3T+7\); the existing single-cap record control gives \(P_1^*/(8NT)\gg L^{-2}\) at this horizon by retaining these stationary births. The criterion at \(T\asymp\sqrt R/L^b\) still requires a new lower estimate. The exact .10/L conditional fraction on the narrower prescribed prime products does not follow from the exchange of both full rough populations.

[Wu, original paper](https://www.impan.pl/shop/publication/transaction/download/product/82961) · [Lichtman, original, §5.1](https://arxiv.org/pdf/2109.02851v2) · [formal first-height bridge and axiom audit](https://github.com/tara-sooo/A166944-Lean/actions/runs/46122447492) · [second brief and definitions](https://github.com/tara-sooo/A166944-Lean/blob/0a06cbc558612c8892eeb1548bc933d01a915567/research/astra-max/2026-11-28-round2-research-brief.md).
