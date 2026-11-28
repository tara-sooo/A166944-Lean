# The specified quotient has at most three prime factors at the target frequency

Issue #10, round 2, 2026-11-28 JST. This note keeps **exactly** the source \(n=pv\), \(p,v\) prime, \(p\in[R^{.374900},R^{.374950}]\), \(R+1\le pv\le2R+1\), from §3.2 of the second brief. Write \(B_R\) for its size, \(L=\log R\), \(b=.313\), \(T=T_b^*\) for all prescribed \((n,q,r)\) divisor incidences (including those outside the boxes used below), and \(s=(n-2)/(qr)\). Let \(\Omega\) count prime factors with multiplicity.

**Unconditional paper deduction.** In every sufficiently large slab,
\[
 \frac{\#\{(n,q,r)\in D_b^*: P^-(s)\ge R^{.09},\ \Omega(s)\le3\}}{T}\ge\frac{.101}{L},\qquad
 \frac{\#\{(n,q,r)\in D_b^*: P^-(s)\ge R^{.08},\ \Omega(s)\le3\}}{T}\ge\frac{.175}{L}.
\]
These inequalities retain primality of both original source factors. A1 demands \(\Omega(s)=1\), which remains open. The separate [bilateral count](https://github.com/tara-sooo/A166944-Lean/blob/86c561d8cf0adfa58e57248fabb562e5c34648f4/research/astra-max/2026-11-28-round2-rough-pairs-past-one-third.md) yields the unconditional .334 stationary first-height exponent on a broader population.

## Programmable placement of the two divisors and a weighted third prime

Write \(t=\log_R q,\ u=\log_R r\). Use disjoint half-open boxes of side .001 in the certificate, with lower endpoints \((t_0,u_0)\) on the milliexponent grid, \(t_0\ge .160,\ u_0\ge .156\), upper endpoints \(t_1,u_1\), \(u_1\le t_0-.001,\ t_1+u_1\le .374\). The exact loops cap \(t_0\le.218,\ u_0\le.188\); all four nontrivial boundaries of \(D_b^*\) are checked against worst endpoints. Only boxes with positive certified lower are used. For one box set
\[
 d=.6245-t_1-u_1,\quad h=1.0001-t_0-u_0,\quad y=.236,\quad z=.08\ \text{or } .09 .
\]
All its quotients have \(s\le R^h\) for large \(R\).

Group **both** divisor primes \(q,r\) into the first modulus factor. To additionally require a prime \(j\mid s\), put \(j\) in the **second** factor, with exponent \(w=\log_R j\in[z,y]\). More explicitly, in a small exponent interval \(w\le w_1\), use ordinary well-factorable sieve remainder components at level \(R^{d-w_1}\). Take their factor support capacities \(R^{.3748-t_1-u_1}\) and \(R^{.2497-w_1}\). After convolving the first coefficient with the two prime-box indicators, and the second with the \(j\)-box indicator, the resulting total factors have respective capacities \(R^{.3748},R^{.2497}\). With \(j\) absent set \(w_1=0\) without appending a prime. Each coefficient is uniformly bounded up to an absolute constant: an integer in one of these ranges has boundedly many prime divisors with exponent \(\ge .08\), and the divisor remaining after choosing the appended factors is determined. One can restrict the weights in each prime box independently.

These two factors fit Pascadi Proposition 4.4 with a unit third factor and the unrestricted short *source prime* \(p\) of exponent at most .374950. In (4.15), the three margins are at least .000100, \(1-2(.374950)-.2497=.000400\), and \(2-2(.374950)-5(.2497)=.001600\), before harmless dyadic constants. Use a sufficiently small fixed power slack. The squarefreeness/sifting-prime restriction on the two *sieve components* is the Möbius common-divisor projection in the earlier project note. Its large-common-divisor tail gains the same \(L^{-K}\) since the extra reciprocal sums over \(q,r,j\) are bounded on these polynomial ranges. The sieve primes lie below \(R^z\); the two original divisors exceed that cutoff. Cases \(j=q\) or \(j=r\) have a large square dividing \(n-2\): their actual contribution even with divisor weights costs \(O(R^{1-.08+o(1)}+R^{1/2+o(1)})\), and their coprime-reference contribution is equally negligible by the square-modulus reciprocal sum. The coprime reference for \(p,v\) can be replaced by the full box mass per reduced class with \(O(R^{1-.37+o(1)})\) error, since a shared source prime is polynomially large and each grouping has bounded multiplicity (or ordinary divisor bounds). One may alternatively retain the reference until after summing each positive/negative main term.

The procedure applies the sieve to a **single aggregate multiset** of quotients for each \(q,r\) box and, where needed, \(j\) bin, so its remainder weights are independent of the individual appended primes. Product-slab restrictions for the source are handled by short multiplicative inner/outer boxes as in the bilateral proof, with the prime number theorem for the bare masses; take inner boxes in positive counts and outer in subtracted counts. Include the fixed positive/negative weight extrema on a \(j\) bin and then take its mesh to zero. The aggregate local model is \(1/(\ell-1)\) at odd sieve primes, with unsifted reference \(B_R\sum_{q,r}1/\phi(qr)\), multiplied also by the \(j\)-reciprocal sum when present. The estimate for the total denominator is the earlier absolute marginal \(T=(J+o(1))B_R,\ .289054\le J<.291\). [Pascadi, (4.15)](https://arxiv.org/html/2505.00653v2#S4) · [Unit and sieve-weight audit](https://github.com/tara-sooo/A166944-Lean/blob/86c561d8cf0adfa58e57248fabb562e5c34648f4/research/astra-max/2026-11-28-round2-rough-pairs-past-one-third.md) · [Exact denominator and two-step Buchstab identity](https://github.com/tara-sooo/A166944-Lean/blob/94eb8d93f287917fdb4d465e7cc52bdd5ae2e9ce/research/2026-11-28-min-negative-variable-cutoff-and-absolute-marginal.md).

## Richert minorant and explicit coefficient

Delete repeated polynomial prime divisors in \(n-2\) as above; each incidence has bounded choice of the appended primes. On \(P^-(s)\ge R^z\) use the weight
\[
 W(s)=1-\frac{1}{4-h/y}\sum_{\substack{j\mid s,\ j\text{ prime}\\R^z\le j<R^y}}
                   (1-\log_R j/y).
\]
Here \(4-h/y>0\). If \(\Omega(s)\ge4\), the sum is at least \(\Omega(s)-\log_R(s)/y\ge4-h/y\). For \(\Omega(s)\le3\), \(W\le1\). Hence the weighted sum lower-bounds the required count. This is the logarithmic Richert weight applied to the actual quotient multiset; the inequality follows pointwise. [Classical weighted-sieve form](https://doi.org/10.1016/j.jnt.2017.08.011).

With \(M_R=4C_2B_R/L\), the unweighted lower for a cell is its mass \(j_{\rm cell}=\log(t_1/t_0)\log(u_1/u_0)\) times \(M_R\log(d/z-1)/d\), up to arbitrarily small relative-to-\(M_R\) errors. Indeed \(2<d/z<4\). For a pin \(j\) of exponent \(w\), upper-sieve after removing it, at exponent \(\min(z,(d-w)/2)\). This upper contains the desired sifted set and is always on the \(2e^\gamma/s_{\rm sieve}\) plateau, since \(d-w>0,\ w\ge z,\ d/z<4\). For a finite \(w\) bin use \(d-w_1\) first. The weight cost per unit of \(M_R j_{\rm cell}\), before multiplying by \(1/(4-h/y)\), is at most
\[
 I=\int_z^y\frac{1-w/y}{w(d-w)}\,dw
 =\frac{\log(y/z)}d+\left(\frac1d-\frac1y\right)\log\frac{d-z}{d-y}.
\]
Thus sum \(j_{\rm cell}\max(0,\log(d/z-1)/d-I/(4-h/y))\). The certificate uses outward rational enclosures for all logarithms, including the negative multiplier in \(I\). For \(z=.08\) the sum is at least .020771201 over 897 retained cells; for \(z=.09\) it is at least .011989835 over 781. Using \(C_2\ge2541/4096\) (keep \(p=3,5,7,11\), and insert all integer factors \(1-1/k^2,\ k\ge12\) in the tail), the corresponding lower coefficients relative to \(T/L\) are .177122335 and .102240969 before fixed approximation errors. This proves the stated bounds with slack. [Executable rational certificate](https://github.com/tara-sooo/A166944-Lean/blob/2dba6391a6e2e13341bab725a79ce0d98d4c79ea/research/lean/negative_min_narrow_quotient_richert.py).

## Feed the lower into the second Buchstab identity and the real clock

If \(S(R^{.313})<.001M_R\), the previously proved inequality \(S(R^b)/M_R\ge F_0(b)+C_R(b)/M_R-\epsilon\) implies \(C_R(b)<.0083M_R\) for all sufficiently large such slabs, by choosing fixed \(\epsilon\) small. Every counted incidence above with \(P^-(s)\ge r\) contributes to \(C_R(b)\). Since \(C_2<1\) and \(J\ge.289054\), the .08 result therefore leaves at least
\[
 (.175\cdot .289-.0083\cdot4-o(1))\, B_R/L > .017\,B_R/L
\]
actual incidences with \(R^{.08}\le P^-(s)<r<q\) and \(\Omega(s)=2\) or 3. A prime quotient has size much larger than \(r\) on every retained cell. Consequently \(n-2\) has exactly four or five prime factors, three of them \(P^-(s),r,q\) below \(R^{.219}\). Each \(n\) contributes at most ten choices of \(q>r\). This is a different failure population from the previously known isolated \(R^{.30}\)-scale factor on the same source.

It can also be made an actual canonical family with a unique separated least factor. Remove integers where the two smallest factors of \(n-2\) have exponent gap below a sufficiently small fixed \(\eta>0\). Enumerate all unrestricted four/five-prime boxes of this kind with exponents at least .08, then upper-sieve the opposite \(n\) at \(R^{.26}\) via Wu Lemma 2.9 at \(4/7-.0001\). The slab-normalized limsup cost is \(O(\eta)\) by bounded simplex densities. Since \(B_R/L\asymp R/L^2\) with a fixed (small) positive constant for the user-specified band, choose \(\eta\) after that constant. This retains \(\gg R/L^2\) distinct canonical centers \(A=n-1\) with first actual minus label \(P^-(s)\): its first opportunity is within \(3P^-(s)/2+O(1)\), whereas every competitor is larger by a fixed power, including the two factors of \(n\). Thus one obtains a real four/five-factor alternative on any slab where the narrow stationary count is small. The sign of the cofactor phase and the size of the **prime-only** numerator are still undetermined.

The two computed integrals concern fixed sieve coefficients. The asymptotic deductions rely on the cited distribution theorems and the weight placements above; neither these deductions nor the prime-only A1 bound have been Lean-verified.
