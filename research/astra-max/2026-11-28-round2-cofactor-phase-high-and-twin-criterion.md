# Cofactor phases give canonical HIGH alternatives and a fixed-power twin criterion

2026-11-28 JST, Issue #10, second round. This uses the [bilateral sieve above one third](https://github.com/tara-sooo/A166944-Lean/blob/86c561d8cf0adfa58e57248fabb562e5c34648f4/research/astra-max/2026-11-28-round2-rough-pairs-past-one-third.md). Write \(\Pi_R=2C_2R/(\log R)^2\), \(L=\log R\). All results below are paper deductions; the finite checks exercise the constants and the clock independently of the asymptotic argument.

## A phase condition that survives reversing the sieve

Fix \(a=.206\). For the right neighbor \(m=A+1\), accept every \(4R^b\)-rough integer, and also accept a \(4R^\ell\)-rough integer with least factor \(p<4R^b\) when \(m/p=3\bmod4\). Call its indicator \(C_+(m)\). Define \(C_-(n)\), \(n=A-1\), the same way with \(n/p=1\bmod4\). These are exactly the two HIGH cofactor residues. The large prime cutoff automatically accepts prime neighbors in our slab. Let \(U=\mathbf1_{P^-\ge R^a}\) and \(E_+=U-C_+\). Pointwise,
\[
 C_-(n) C_+(m)= C_-(n)U(m)- E_+(m)C_-(n).
\]
In the subtracted term, \(C_-(n)\le\mathbf1_{P^-(n)\ge4R^\ell}\). The upper sieve is on its plateau already at the **lower** cutoff \(\ell\). This allows the phase condition on the opposite neighbor to be dropped from the upper bound. In the positive term enumerate the accepted left side, retaining its phase.

Each sign's unsifted mass in units \(R/L\) tends to
\[
 J=(M(\ell)+M(b))/2,\qquad M(t)=\omega(1/t)/t.
\]
Indeed all the numbers between the thresholds are composite and the cofactor \(u=n/p\) is equidistributed between its two odd residues. On each ordered prime-factor box this is the prime number theorem in the two residue classes applied to one of the cofactor primes and summed over the others. Discard equal or same-bin factors by the limiting simplex argument. This computation is performed **before** the shift sieve. In a phase-restricted product row take the unrestricted *least prime* as the short variable and impose the residue constraint only on the long product. In particular, a short prime restricted modulo 4 is never asserted to be Siegel–Walfisz.

For \(3/14<\ell<1/3,\ b=.35\) or .4, positive phase rows with short exponent \(t\in[\ell,b]\) have level \(d_0=4/7-.0001\) by Wu Lemma 2.5 (take the minimum in his table on \([3/14,2/5]\)). The unfiltered rows use Lemmas 2.7 and 2.9. For negative rows with \(t\le1/3\), use the upper level \(d_U=.5999\) established in the preceding note. For \(1/3\le t\le .4\) the ordinary two-factor level \(\min\{(2+3t)/5,1-t\}\ge .6\) suffices. Endpoints within \(O(1/L)\) are absorbed by the fixed exponent slack. The limiting lower coefficient is at least
\[
 J B(d_0)-2(M(a)-J)/d_U,\qquad B(d)=2\log(d/a-1)/d.
\]
For \(b=1/2\), the cutoff \(4\sqrt R\) accepts exactly the prime neighbors among the high-cutoff class. On the remaining balanced semiprime rows \(2/5<t<1/2\) use \(d_B=.4999\) for either sign of the sieve (Wu Lemma 2.5). The extra deduction from the displayed lower is
\[
 \tfrac12\log(3/2)\,[B(d_0)-B(d_B)+2/d_B-2/d_U].
\]
Exactly half of this balanced range is present in each of the positive and negative populations. All upper cutoffs \(\ell\) here have \(1<d/\ell<3\). The analytic sieve approximation errors can be taken arbitrarily small with parameters fixed before the limit.

For the computations take \(M(a)\le.561522/a\) and
\[
 M(\ell)\ \ge\ 1+\log((1-\ell)/\ell)+
 \int_\ell^{1/3}\frac{\log((1-2t)/t)}{t(1-t)}\,dt .
\]
This counts primes, ordered semiprimes, and ordered triples; four-prime terms are nonnegative. Integrating the second-smallest exponent from \(t\) to \((1-t)/2\) gives the numerator logarithm. The integrand is decreasing on the indicated interval, so right endpoints of 200 equal rational cells with lower log bounds certify the following.

| Least exponent \(\ell\) | Target exponent \(b\) | Certified pre-error lower coefficient of \(\Pi_R\) | Usable coefficient after deleting exceptions |
|---|---|---|---|
| .28 | .4 | .011662575 | .010 |
| .312 | .35 | .040241490 | .030 |
| .223 | .5 | .040726796 | .035 |

## From a phase count to an actual first firing

Remove points having two factors on the same neighbor with the second-smallest at most four times the least. Among products with every factor \(\ge4R^\ell\) this is a zero-volume diagonal in the limiting exponent simplex (for semiprimes it is the balanced endpoint). To justify removal at the **two-sided** scale, enclose the logarithmic diagonal in a fixed strip of width \(\eta\), enumerate all its unrestricted prime-product boxes, and upper-sieve the other neighbor at \(4R^\ell\) with Wu Lemmas 2.7, 2.9. The resulting limsup in units \(\Pi_R\) is \(O_\ell(\eta)\), since the fixed finitely many simplex densities are bounded away from exponent zero. Now let \(\eta\) tend to zero. Prime powers can also be deleted by the square-divisor bound.

At a canonical birth, the earliest plus opportunity for a factor \(p\mid A+1\) of cofactor \(u\), with \(p\) large, has age \(((u\bmod4)p-7)/2\). The earliest minus opportunity for \(p\mid A-1\) has age \((((u+2)\bmod4)p-1)/2\), where the odd representatives are 1 and 3. These follow by doubling the absolute clock congruences. Once the intra-neighbor diagonal has been removed, a nonleast factor on either side cannot beat the least on that same side: its earliest age is at least \((4p-7)/2\), above the latest first opportunity of the least one. Thus the real first winner is a least factor of its side. Any factor \(\ge4R^b\) has no opportunity before the first stationary crossing of \(\lfloor R^b\rfloor\). A smaller winner has the specified HIGH phase, with first-event data
\[
\begin{array}{c|c|c|c}
 &\text{age}&x_0&h_0\\ \hline
 +&(3p-7)/2&p(u-1)&p\\
 -&(3p-1)/2&p(u-1)+2&p+3 .
\end{array}
\]
Both neighbors are odd and free of 3, hence \(6\mid A\).

Consequently at \(b=.4\), each sufficiently large slab has a combined family of at least \(.010\Pi_R\) distinct canonical roots. Each either actually reaches \(H=\lfloor R^{.4}\rfloor\) at its birth site with zero gain, or executes a HIGH first firing before that hit, with \(4R^{.28}\le p\le (2/3)H+O(1)\). The analogous assertion at \(b=.35\) has lower coefficient .030 and \(p\ge4R^{.312}\). At least half the corresponding lower bound belongs to one branch in each slab. The first branch counts distinct sites. In the HIGH branch, for a fixed sign and position, \(p\mid x_0\) or \(p\mid x_0-2\) and \(A=x_0+p-1\); the number of possible such polynomial-size prime divisors is \(O_\ell(1)\). It therefore gives a density-scale set of distinct occupied HIGH positions. This counts actual positions, with bounded reverse multiplicity.

For \(b=1/2\) one can instead let each accepted root run until the first event of a composite neighbor. If either neighbor is composite its least prime is at most \(\sqrt{2R+1}\); at an accepted point its opportunity is HIGH. Both prime neighbors have earliest opportunities of order \(R\). Thus there are at least \(.035\Pi_R\) roots that either are twin centers or actually enter HIGH with \(p\ge4R^{.223}\). To restrict the HIGH branch to a fixed upper exponent less than \(1/2\), discard the same-side semiprime strip \(p>R^{1/2-\eta}\) by the preceding diagonal argument with \(O(\eta)\Pi_R\) cost. Fix sufficiently small positive \(\eta\) before taking \(R\) large.

In every density-scale HIGH branch take the more frequent sign. Its \(p,u,pu\mp2\) are all \(R^\ell\)-rough, \(p\) is prime and belongs to a fixed range of upper exponent \(<1/2\), and the pin is the actual first canonical HIGH pin. The hypotheses of the existing common-time theorem are therefore fulfilled. It gives a density-scale subfamily, a fixed \(\tau>0\), and \(\lfloor\tau L^2/2\rfloor\) **subsequent real ticks** at height \((1-o(1))p\), suffix displacement \(O(L^3/\log L)\), pairwise disjoint visited physical states, and a number of additional events tending to infinity. In particular it gives \(\Omega(R)\) distinct occupied physical states in that case. The polynomial time/gain stopping theorem can also start here; its gain branch may descend. Neither the common time nor that stopping alternative proves growth to \(H\). [Adaptive HIGH theorem, §7](https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-adaptive-high-transcript-and-quadratic-time.md) · [Polynomial stopped transport](https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-polynomial-stopped-high-and-record-ladders.md).

## A quantitative target for a direct proof of twin infinitude

Let \(2/5\le\theta<1/2\), \(H=\lfloor R^\theta\rfloor\), and fix \(0\le\beta<8/13\). Count distinct canonical first-\(H\) positions with a witness having \(G\le\beta H\). The number of **non-twin** positions among them is at most
\[
 (K(\theta)+o(1))\Pi_R,\qquad
 K(\theta)=4\left(2-\frac1{1-\theta}+\log\frac{1-\theta}{\theta}\right).
\]
To see this, apply the project's mod-2310 complete-block estimate \(W\le17G/8+395/12\). Elapsed time is \(W+I=H-3+G/2\); the final idle segment thus has length \(I\ge(1-13\beta/8)H-O(1)\). Its exact calendar gives \(I<2q_{\min}(x)\). Both neighbors of the terminal site \(x\) are rough to a fixed positive multiple of \(H\). Dropping the extra slab strip of width \(O(H)\) costs \(o(\Pi_R)\). At a non-twin site at least one neighbor is a semiprime \(pv\) with smaller exponent \(t\in[\theta-o(1),1/2+o(1)]\). For \(2/5\le t\le1/2\), Wu Lemma 2.5 on the unrestricted short prime gives \(d=1-t-\epsilon\). Sieve the opposite neighbor just to \(R^{1/4}\), which contains all the required points, with upper coefficient \(2/d\). The differential mass is \(dt/[t(1-t)]\). Summing both orientations and then letting the fixed slack and cell width tend to zero gives \(4\int_\theta^{1/2}dt/[t(1-t)^2]=K(\theta)\). Thin endpoint strips are harmless by the same box argument. The proof allows arbitrary event counts. [Project clock and potential estimates](https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-mod2310-and-single-cap-gain-record.md) · [Wu, Lemma 2.5](https://www.impan.pl/shop/publication/transaction/download/product/82961).

For example, \(K(.49)<.32\) and \(K(.4999)<.0032\). The unconditional .334 seed theorem supplies at least \(.005\Pi_R\) distinct roots in every large slab. If, along infinitely many unbounded slabs, at least two thirds of a family of this size produce **distinct** first hits at exponent .4999 with \(G\le.6H\), the excess over \(.0032\Pi_R\) proves twin infinitude. The distinct-target survival bound is open. The first-\(H\) alternative at exponent .4 also leaves open which branch carries the density there, and the prescribed A1 numerator remains unevaluated.

[Executable rational bounds and clock check](https://github.com/tara-sooo/A166944-Lean/blob/10f1ebd44bad1d8ee51a7c7c20694b2734dc841c/research/lean/negative_min_bilateral_rough_bounds.py). In the finite clock proxy \(100000\le A\le200000,\ 6\mid A,\ H=100\), explicit divisor and tick enumeration across the selected roots gave 1312 stationary crossings, 798 HIGH plus and 809 HIGH minus first firings. These verify the arithmetic-to-clock bridge on that proxy. The analytic lower bounds are the sieve deductions above.
