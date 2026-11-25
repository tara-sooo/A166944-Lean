# Four-form rough-landing sieve and linear isolation of moderately thick high strands

2026-11-25 JST. Continues [09559cdebe9d](https://github.com/tara-sooo/A166944-Lean/blob/09559cdebe9d44a0a2b5f6a64299e49eeaa1453a/research/2026-11-25-min-unified-deficit-packing.md), on research/min-unified-record-hall-tail-2026-11-25. New unconditional linear removal of high events on moderately sized stable strands when there is a rough horizon immediately after the selected jump, or in a polylogarithmic neighborhood beyond it. This uses four distinct linear forms on the quotient by the selected prime. Also pays the later rough horizon at small synchronous mass, and forces intervening non-HIGH gain on the actual residual path. The newest independent prime-root branch d186d3fa17ef treats asynchronous same-label far lags via exit rank; we do not require that quadratic residual. The independent stable-heavy branch 64323f51c0aa treats recorded stationary arrival geometry at a different gain scale; no transfer of its short-clock constants. No general tail bound or twin-prime proof.

## 1. Parameters and arithmetic support

Retain the original long prime-root ensemble with X dyadic, B=ceil(sqrt(7X)), u=log B, ell=1+log u, N=Theta(X/u), T=floor(X/u^.25), H=T+B, Q=ceil(B/u). Natural HIGH has selected p>=Q and least eligible r(C)>p/sqrt(log p). Every actual completed gain is p-1 and wait w<=2r<=3(p-1). A true tick (j,C) counts b(C,j) original tags in completed waits, excluding terminal snapshots; 0<=2j-C<=6+5H. Thus at any fixed C there are O(H) possible occupied tick states, regardless of how many different recorded arrivals occurred. No original trajectory is changed.

Define rough at scale R=B^(1/8) to mean that neither C-1 nor C+1 has an odd prime divisor <R. Twin horizons qualify. Eventually every natural HIGH prehorizon is rough at this scale. Let L=2 floor(u^(5/4)/2), an even integer. Define a RELAXED arithmetic relation of triples (C,p,e):
    C even in the original O(X) horizon range,
    Q<=p<=B prime, p|(C-1)(C+1), r(C)>p/sqrt(log p) (or no small divisor),
    e even, 0<=e<=L,
    J=C+p-1+e is rough at R.
Only actual high C are needed; for an unambiguous relaxed test require r(C)>p/sqrt(log p) with r=0 interpreted as no eligible prime. Since p is eligible at C, the latter exception does not occur. We can also restrict J to the original horizon domain, which contains all actual completed vertices. Let Fwd be the set of first horizons C of these triples and Back their later horizons J. The same arithmetic triple may witness many original paths or none. Counting triples is an upper bound on BOTH support cardinalities, not on tag multiplicities.

Fix p, e and the unique sign sigma in {-1,+1} such that p|(C+sigma). Write C=p(2k+1)-sigma. The four linear forms in k, expressed using a=2k+1, are
    a,
    p a-2 sigma,
    p a+p+e-sigma-2,
    p a+p+e-sigma.
They are respectively (C+sigma)/p, C-sigma, J-1, J+1. All four avoid odd prime divisors <R for every supported triple: the first two by high least-factor roughness and the last two by the condition at J. Eventually R<p/sqrt(log p) for all p>=Q. The k interval has length O(X/p+1).

For a prime q>=7 not dividing p or any pairwise difference among
    0, -2 sigma, p+e-sigma-2, p+e-sigma,
the four forms exclude EXACTLY four distinct residues mod q. All differences are nonzero for large X, since p>=Q>>L, p>=7 and e>=0. Their product times p is a nonzero integer Delta with log |Delta|=O(u) uniformly. We simply drop the bad primes q|Delta (and q=2,3,5); this can only enlarge the counted set. This is the new dimension-four quotient sieve, not two independent applications of the old dimension-two bound.

## 2. Uniform elementary Selberg upper bound (included proof)

For completeness derive the exact sieve bound needed here, using the classical elementary prime-sum estimates Mertens and sum_(q<=y) log(q)/q=O(log y). Let z=floor(B^(1/20)). Use only good primes q<=z (so q<R eventually). For squarefree d made up of those primes put omega(d)=4^omega_number(d), g(d)=omega(d)/d, h(d)=prod_(q|d)(1/g(q)-1), with empty values 1. The residue counts multiply by CRT.

Let G=sum_(d<=z) 1/h(d) over these squarefree d. Choose y_k=mu(k)/(h(k)G) for the same index set, and define
    lambda_d g(d)=sum_(k<=z,d|k) mu(k/d)y_k,
with lambda zero outside the index set. Then lambda_1=1. The finite quadratic identity
    sum_(d,e) lambda_d lambda_e g(lcm(d,e))
      =sum_k h(k) (sum_(d:k|d) lambda_d g(d))^2 =1/G
follows since g(lcm)=g(d)g(e)/g(gcd), and 1/g(gcd)=sum_(k|gcd)h(k). The chosen y_k is recovered by finite Mobius inversion. Moreover
    |lambda_d| <= 1/[g(d)h(d)] <= d.
Indeed the sum over k=d m in absolute value is <=G/h(d), and for q>=7 each factor (1-4/q)^(-1)<=q. If an integer k avoids all forbidden good-prime residues, its sum of lambda_d over satisfied forbidden-residue conditions is exactly lambda_1=1. For every other integer the square is nonnegative. Expanding this square over a length V interval therefore gives an upper bound
    V/G + O(z^8).
The error is uniform: each CRT residue class count differs from V/lcm by <=1; at most z^2 pairs, weights <=z^2 in product, omega(lcm)<=lcm<=z^2, so even z^6 suffices. The weaker z^8 is convenient.

To lower bound G, let y=z^a for a sufficiently small fixed a>0. On subsets of good primes <=y use the probability distribution proportional to 1/h(d), with independent inclusion probabilities g(q)=4/q. The expectation of log d is sum_(q<=y, good)4 log q/q <=C log y <=(log z)/2 by choice of a. Markov shows at least half of the product weight lies on d<=z. Hence
    G >= .5 prod_(q<=y, good) (1-4/q)^(-1).
Mertens gives the full product lower bound c(log y)^4 after dropping 2,3,5. The loss from bad primes dividing Delta is at most O(ell^4): primes <=u^2 contribute at most O((log(2+u))^4), by Mertens and convergence of sum 1/q^2 in log(1-4/q)^(-1)-4 log(1-1/q)^(-1); primes >u^2 dividing Delta have total reciprocal O(u/u^2), since log |Delta|=O(u). Thus G>>u^4/ell^4 uniformly in p,e,sigma. With V=O(X/p+1) and z^8<=B^.4, the error is absorbed into X ell^4/(p u^4) since X/p>>B. The required count for fixed p,e,sigma is
    O(X ell^4/(p u^4)).                                   (1)
No primality assumption on any of the four forms, no independent residue distribution on actual trajectories, and no unproved multi-form asymptotic are used.

Sum (1) over p>=Q (sum 1/p=O(ell/u) by the elementary prime interval reciprocal bound used in minfactor-support) and over e. Obtain
    # triples, |Fwd|, |Back| << X (L+1) ell^5/u^5.          (2)
This includes the boundary e=0 (immediate landing) and all even offsets through L. No multiplier for actual arrival ticks or ancestor tags in (2).

## 3. Unconditional linear clock mask at moderate mass

Let Mstar=2 u^(7/3)/ell^2. Pay all natural HIGH clock ticks at C in Fwd with original b(C,j)<=Mstar. Independently pay all completed clock ticks, even non-HIGH, at C in Back with b(C,j)<=Mstar, by disjoint priority. The full support estimate (2) and O(H) tick states per horizon give
    W_isolation << Mstar H X (L+1) ell^5/u^5
                = O(NT ell^3/u^(5/12)) = o(NT).          (3)
Indeed Mstar has exponent 7/3, L has exponent 5/4, and the normalized exponent is 7/3+5/4-4=-5/12. This is a LINEAR actual-clock estimate on the entire original ensemble; no synchronous pair energy, no Hall mass, and no async condition. It remains valid after arbitrary previous tick or incidence masks. The sieve can be used directly without computing actual triples on large windows.

By the parent entropy-window construction, for every retained focal HIGH tick in a stable group g with n_g<=m_h u^(1/3)=u^(7/3)/ell^2, the full original tick mass is at most n_g/(1-delta), delta=exp(1/ell)/ell=o(1). Hence it is <=Mstar eventually. A surviving HIGH tick in such a moderate strand cannot have its prehorizon in Fwd or Back. In particular, for its actual selected label p,
    all even J in [C+p-1, C+p-1+L] are NOT rough at R,    (4)
provided J lies in the original horizon domain. This statement is arithmetic, not just about the next actual vertex. In the middle of a stable span the complete interval is in the domain. Each such J has an odd factor <B^(1/8) in J-1 or J+1. At the actual immediate posthorizon the least eligible factor is therefore <B^(1/8) and a twin stop is impossible there. An actual next completed event (if present) has wait <=2B^(1/8). The next natural HIGH hit on the actual trajectory, if it exists, must have prehorizon exceeding C+p-1+L. All intervening events until the next natural HIGH are non-HIGH; their total selected gain exceeds L. This includes relative-cheap events of large selected label, which must not be confused with small selected labels.

If an intervening block used only labels <=y0 where the even primorial of those labels P0<=L, it could not strictly cross the first multiple of P0 at or above its initial horizon; its total gain would be <P0. The proof is the ordinary primorial barrier from the stable strand note. Thus at least one intervening non-HIGH label exceeds y0, where y0=Theta(log L)=Theta(log u) using the largest even primorial <=L and Chebyshev. The actual outgoing high event is isolated even though its witness interval of length >=B^(3/2) contains many high labels.

For a larger uniform mass cap m, the same count with L fixed yields general cost O(NT m(L+1)ell^5/u^4). Thus for immediate rough landing only (L=0), one can pay all such high ticks with b<=u^(15/4)/ell^5 at cost O(NT/u^.25). This optional cap is substantially larger than moderate mass but still polylogarithmic; no claim for all RESET-scale large groups.

## 4. Exact residual and limitations

Keep all previous actual linear masks and add (3) by priority. In the previous sufficient condition liminf (A_new+L_new)/(NT)<1/2, replace the two residual clocks with their subsets after these new deletions. Same no-twin contradiction, same gain-stopped ensemble, no modified dynamics. Moderate HIGH stable strands are now constrained simultaneously by:
* long nonRESET excursion and high deficit (previous note),
* local frozen high-label and adjusted-phase diversity (previous note; those witnesses need not survive the new mask),
* every surviving HIGH selected jump lands in a full polylogarithmic interval with no R-rough horizon, and the next actual natural HIGH event has a non-HIGH intervening gain >L.

The last statement concerns each surviving hit and all actual next high hits, even if those next hits are subsequently deleted. To obtain diversity of the new residual itself one could freeze a new measure after the present deletion and repeat the previous sparse-interval cover (one additional absolute O(NT/u^.25) payment). This is valid because the present mask depends only on original tick states and arithmetic support and the prior entropy mask is not needed to define it. It gives the previous local diversity conclusions with the NEW frozen measure, on moderate stable spans. All global masks still apply only a fixed number of times, not indefinitely for free.

These constraints do not bound the total remaining occupation. In particular intervening gain >L is much smaller than the size of a high gain p-1>=Q-1, so it is not enough by itself to charge all high clock to the medium clock. The remaining large-mass stable strands and non-HIGH clock are also open. No Lean compilation and no external novelty claim. Main and independent branches unchanged.
