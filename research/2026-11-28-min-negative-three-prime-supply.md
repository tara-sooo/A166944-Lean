# Negative MIN: using a different prime for distribution and first firing

2026-11-28 JST, Issue #10. Base 57ed19ed4c6925c80599bc7e7cd43ecba5ee8aab. Paper deductions from published sieve estimates and the branch's exact calendar. The statements concern every sufficiently large slab. Constants may depend on the fixed exponent. No twin or M85 assertion.

## 1. A non-twin population up to every fixed exponent below 3/10

Write \(L=\log R\). For any fixed \(0<\sigma<3/10\) there are \(\gg_\sigma R/L^2\) distinct \(A\in[R,2R]\cap 6\mathbb Z\) for which \(A+1=pvu\) is the product of three distinct primes. Their actual first firing has label \(p>4R^\sigma\), and \(P^-(A-1)>3p\). The birth reaches \(\lfloor R^\sigma\rfloor\) with displacement zero. This construction controls the winning label, including for populations containing no twin centers.

**Proof.** Choose a small fixed \(\delta>0\) with \(\sigma<.3-4\delta\), and for definiteness \(\delta<.001\). Choose disjoint dyadic bands for \(p\) and \(u\), with lower endpoints \(P,N\), respectively, in
\[
 .3-3\delta<\log_R P<.3-2\delta,\qquad .4-\delta<\log_R N<.4 .
\]
Use a grid of powers of two and omit edge boxes if necessary. Let \(V=R/(PN),\,M=R/N\). Choose primes
\[
 P<p\le1.1P,\quad N<u\le1.1N,\quad 1.1V<v\le1.2V .
\]
Then \(m=pv\in(M,2M]\), \(A+1=mu\in(1.1R,1.452R]\), and \(p<v<u\) for large \(R\). We may fix \(p\equiv1\bmod 6\). For each box the coefficient of \(m\) is the indicator of these products, with a unique representation. The short sequence is the unrestricted prime indicator on the stated \(u\) interval. The product population in the box is \(B\asymp R/L^3\) by the prime number theorem in fixed progressions.

Apply J. Wu, *Chen's double sieve, Goldbach's conjecture and the twin prime problem*, Acta Arith. 114 (2004), 215–273, Lemma 2.5, printed pp. 221–222, (i),(ii), with \(X=MN=R\), \(a=2\), short exponent \(\nu=\log_R N\). On this branch of the table the distribution exponent is \((2+\nu)/4>.6-\delta/4\). Choose \(D=R^{.6-\delta}\), with distribution loss \(\delta/4\). Both coefficient sequences are 1-bounded. The short prime sequence satisfies the coprime Siegel–Walfisz condition by subtracting endpoint estimates for log-power moduli. For larger moduli use the trivial progression bound \(N/q+1\) and \(N/\phi(q)\) (use \(\phi(q)\gg\sqrt q\) and choose the log-power cutoff sufficiently large). Removing primes dividing the auxiliary integer costs \(O(\omega(d))\), absorbed by the divisor factor. Short primes exceed the least-factor cutoff in (ii). The restricted progression is on the long variable only.

Sieve \(mu-2\) at \(z=4R^{.3-2\delta}\) by the ordinary lower linear sieve, Wu Lemma 2.2, (2.3),(2.5),(2.6). Use odd primes and \(g(d)=1/\phi(d)\) on squarefree odd sieve divisors. Then \(V(z)\asymp1/\log z\) by Mertens, and \(\log D/\log z>2\) with fixed slack. Choose the fixed sieve approximation error sufficiently small after this slack. The remainder weights are the ordinary well-factorable order-one components for this sifting set; use their zero extensions, as in Lichtman (5.14)–(5.20), without applying a mask to an arbitrary factorable sequence. The congruence theorem uses the coprime main term. Replacing it by \(B/\phi(d)\) costs in absolute sum at most
\[
 B\max_{pvu}\sum_{\ell\mid pvu}\sum_{\substack{d\le D\\\ell\mid d\\d\ {\rm squarefree}}}1/\phi(d)
 \ll B L R^{-(.3-3\delta)}.
\]
Here \(\sum_{e\le D}1/\phi(e)\ll\log(2D)\); sum over all three prime factors even when a factor lies under the sifting limit. Thus each box supplies \(\gg R/L^4\). There are \(\gg_\delta L^2\) pairs of bands. Prime ordering and disjoint bands give unique roots, and \(4R^{.3-2\delta}>3p\) even at a box edge. The other two factors exceed \(4p\) for large \(R\). The sifted product is odd and equals 1 modulo 3, since \(3\nmid pvu(pvu-2)\). Therefore \(A=pvu-1\) is canonical.

The first possible plus tick for \(p\) has wait \(w=((uv\bmod4)p-7)/2\). Any candidate through that tick has label \(\le 2w+7\le3p\); \(p\) is the unique available spatial factor in this range. The first destination is \(p(uv-1)\), at height 0 or \(p\), according as \(uv\bmod4=1\) or 3. Thus \(q_{\min}(A)=p\), and all these \(A\)'s are stationary through the claimed height. No separate density in either residue class is assumed. Since \(p\equiv1\bmod6\), every first destination is divisible by 6.

## 2. Use after the first firing

Take \(\theta=.3-3\delta,\rho=.18\) in the branch's growing-depth separation theorem, with any fixed \(0<c<1\). Its hypotheses are a canonical non-twin root, \(q_{\min}\ge R^\theta\), and an actual first plus winner \(p\le R^{1/2-\rho}\); primality of \((A+1)/p\) is not required. For all but \(o(R/L^2)\) roots there are \(k=\lfloor c\log L/\log\log L\rfloor\) additional actual firings. The visited positions through these firings are disjoint between retained roots. All \(k+1\) post-first positions have \(q_{\min}<K=\lfloor R^{\rho/(4k)}/L^5\rfloor\); the extra labels are at most \(Z=R^{\rho/(4k)}\). This yields \(\gg_\sigma Rk/L^2\) distinct visited positions and retires the prefixes by age \(3p/2+2kK\). On the high branch the post-first height stays at least \(p-kZ/2\). The theorem does not decide the split between the two branches or push those prefixes to height \(R^{2/5}\).

**Source locators.** [Wu, original PDF, pp. 219–222](https://www.impan.pl/shop/publication/transaction/download/product/82961); [Lichtman, §5.1 and (5.20)](https://arxiv.org/pdf/2109.02851v2); [branch growing-depth theorem, §§1–5](https://github.com/tara-sooo/A166944-Lean/blob/4f654dfe616a0e0d88048ecf5d67bbe68944d8ef/research/2026-11-28-min-negative-growing-depth-orbit-separation.md); [prior single-prime seed](https://github.com/tara-sooo/A166944-Lean/blob/c20b70c398f0e2165e08da694790dacc1b724d50/research/2026-11-28-min-negative-product-sieve-canonical-supply-and-reverse-ancestry.md). Source scope and constants checked 2026-11-28 JST. This argument for three-prime centers does not rely on the branch's appended-prime weight draft or on a rough Chen prime-pair claim.
