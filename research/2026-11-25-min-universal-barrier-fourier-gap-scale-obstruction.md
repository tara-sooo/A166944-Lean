# Universal LOW barriers: Fourier gap bounds and the scale obstruction

2026-11-25 JST. Continues 930bde4315c87781bcf0a59cd4960199724eec2e on the SAME research/min-cycle-forest-2026-11-24 branch. Original Fourier/CRT deductions and complete-period barrier enumeration using a sparse interval sweep. No external research, no Lean compilation. This gives a genuine exponential-in-number-of-primes improvement over the primorial-period gap bound, but not the LOW potential convergence needed in the physical stopping theorem.

## 1. Normalize to the even-horizon lattice

Let Y>=5, primes 3<=p<Y, r_Y their number, P=product p, L=2P. In this note P is the ODD primorial, NOT the secondary prime cutoff called P in the previous eta estimate. Write C=2x. The universal barrier condition in the preceding note is precisely
    x mod p in {0,1,...,m_p-1}, m_p=(p-1)/2, for every p<Y.
Let f(x) be its indicator on Z/PZ, b=product m_p, density delta=b/P. A uniform x mod P corresponds to a uniform even C mod L, independently of the initial time coordinate. This condition blocks every eligible jump with p<Y, including those not chosen by MIN. The forward distance G(x) is the least nonnegative integer j such that f(x+j)=1. Include the current point if it is a barrier. All distances below are in half-horizon units; multiply by 2 for actual C increments. The low-only ghost has cumulative gain at most 2G, total elapsed <=3 times gain, and maximum signed attained-event height increment D_Y<=10G, by the preceding monotone-gain lemma. This includes the terminal case G=0.

## 2. Exact Fourier factorization and local bounds

For k mod P write Fhat(k)=P^-1 sum_x f(x) exp(-2pi i kx/P). CRT gives a product of local transforms on Z/pZ with frequency k times the inverse of P/p modulo p. Normalize by Fhat(0)=delta. For a local nonzero frequency l,
    |(1/m_p) sum_(x=0..m_p-1) exp(-2pi i l x/p)|
       = |sin(pi m_p l/p)|/(m_p |sin(pi l/p)|)
       <= c_p=min(1, 1/(m_p sin(pi/p))).
For a zero local frequency the ratio is 1. Since the CRT multiplier is invertible modulo p, the local frequency vanishes iff p|k. Consequently
    |Fhat(k)/delta| <= product_(p not dividing k) c_p.
Put
    beta_Y=product_p [c_p^2+(1-c_p^2)/p],
    gamma_Y=product_p [c_p+(1-c_p)/p].
In particular c_3=1. For large p, c_p=(2/pi)(1+1/p+O(1/p^2)). Thus
    beta_Y=Theta((4/pi^2)^r_Y (log Y)^(1+pi^2/4)),
    gamma_Y=Theta((2/pi)^r_Y (log Y)^(pi/2)).
The constants are independent of Y. This follows by taking logs and using the classical Mertens harmonic-prime estimate (the O(1/p^2) errors sum absolutely). In particular both products tend to zero. These are explicit products, not a fitted statistical model.

## 3. A uniform forward-gap probability bound

For integer R>=1 let N_R(x)=sum_(j=0..R-1) f(x+j). E N_R=R delta. By Fourier orthogonality,
    Var(N_R)/(R delta)^2
      = sum_(1<=k<P) |Fhat(k)/delta|^2 |A_R(k)|^2,
    A_R(k)=R^-1 sum_(j=0..R-1) exp(2pi i kj/P).
For 1<=k<=P/2, |A_R(k)|<=min(1,P/(2Rk)), by the geometric-series formula and sin(pi k/P)>=2k/P. Reflect the other half of the frequencies. Define nonnegative g(d)=product_(p|d)(c_p^-2-1) for d|P, with g(1)=1. Then
    product_(p not dividing k)c_p^2
      = (product_p c_p^2) sum_(d|gcd(k,P)) g(d).
The sum over positive multiples k=dj is at most
    sum_(j>=1) min(1,(P/(2Rdj))^2) <= P/(Rd),
using the integral of the nonincreasing function min(1,(P/(2Rd x))^2) over x>0. Summing divisors and both halves gives the uniform explicit inequality
    Var(N_R)/(R delta)^2 <= (2P/R) beta_Y.
Chebyshev at N_R=0 yields
    Pr(G>=R)=Pr(N_R=0) <= min(1,2P beta_Y/R).
This holds for uniform horizon phase only; it does not posit uniformity of arbitrary adaptively chosen arrivals. In particular G/(P beta_Y) is tight and G/P->0 in probability. For example R=ceil(P sqrt(beta_Y)) gives Pr(G>=R)<=2 sqrt(beta_Y). This is an exponential relative improvement over the previous deterministic bound G<P, even though its absolute size is still very large.

For completeness, the analogous L1 sum using c_p^-1-1, and sum_(j<=P/(2d)) 1/j<=1+log P, yields the pointwise discrepancy bound
    |N_R(x)/(R delta)-1| <= (P/R)(1+log P) gamma_Y.
No character sum estimate about the locations of primes is required. The gap bound in the next section is stronger than the resulting L1 maximum-gap consequence.

## 4. Maximum gap, forward mean, and selected-cell widths

Let g_i be the consecutive cyclic barrier gaps in half-horizon units; sum g_i=P. The following exact identity needs no Fourier:
    # {x:G(x)>=R} = sum_i (g_i-R)_+,
because each gap contributes the indicated number of starts whose R tested positions contain no barrier. Therefore
    sum_i (g_i-R)_+ <= 2P^2 beta_Y/R.
For an individual gap g>=2 take R=floor(g/2). Its contribution implies R(g-R)<=2P^2 beta_Y, and R(g-R)>= (g^2-1)/4. The same resulting bound trivially covers g=1. Thus
    max_i g_i <= min(P,sqrt(8P^2 beta_Y+1)).
In actual horizon units the maximum barrier spacing is at most 2 sqrt(8P^2 beta_Y+1). Its ratio to L is O(sqrt(beta_Y)). Also
    E G = sum_i g_i(g_i-1)/(2P) = sum_(R>=1) Pr(G>=R).
If A=2P beta_Y<P, the upper bound by the integral of min(1,A/x) on [0,P] yields
    E G <= A(1+log(P/A)).
If A>=P use E G<=P. In particular E G=O(P beta_Y (1+r_Y)) for large Y.

For any j selected cells in a whole period (arbitrary selection, no random arrival assumption), their total width in half-horizon units is bounded by
    sum_selected g_i <= jR + 2P^2 beta_Y/R
for every integer R>=1. This follows by splitting each g_i into min(g_i,R)+(g_i-R)_+. For j>=1 choose R=ceil(P sqrt(2 beta_Y/j)), or R=1 if that is less than one, obtaining O(j+P sqrt(j beta_Y)). This provides a selected-cell width bound without assuming equal spacing or uniform incoming mass. Across several full periods the same tail sum scales by the number of periods; a partial period can be overcounted by a full one. These bounds are independent of all clocks.

## 5. What these bounds do and do not give for the LOW coefficient

From D_Y<=10G and the forward tail,
    Pr(D_Y>K) <= min(1, 2P beta_Y/(floor(K/10)+1))
for K>=0, since D_Y>K forces integer G>=floor(K/10)+1. In particular the deterministic maximum of D_Y is O(P sqrt(beta_Y)+1)=o(P). For the sequence of observation scales S=P this gives D_(Y,2S)/S->0 uniformly for the finite alphabet <Y. This is NOT the infinite-CRT signed-peak limit: the coupling error available from the common CRT construction is O(S/(Y log Y)), which is not small at S=P. Likewise the full-ghost clipped potential method needs a K=o(Y log Y) with Pr(D_Y>K)->0, and the new upper bound is not small there.

In fact there is a simple quantitative obstruction to using universal-barrier geometry ALONE on that scale. The union bound gives
    Pr(G<R) <= R delta
       = O(R 2^(-r_Y)/log Y),
by delta=2^(-r_Y) product_(3<=p<Y)(1-1/p). For R=O(Y log Y) this tends to zero. Thus a uniform start is with probability tending to one farther than every fixed multiple of Y log Y from the next universal barrier. This is a statement about the permissive barrier set, not a lower bound on actual signed peaks or lifetimes: the actual clock dynamics may terminate or acquire negative height long before reaching it. In particular the barrier-based upper majorant 10G itself cannot be made o_prob(Y log Y). No disproof of eta->0, and no new proof of it. The preceding height-adaptive cost theorem and physical far-pair target are unchanged. The new quantitative geometric bound is usable for smaller alphabets, where the barrier scale is below a chosen observation time, but controlling selections of the other labels remains essential.

## 6. Finite complete-period diagnostic

Saved research/min_universal_barrier_fourier_gap_audit.mjs and results JSON; exact remote readback at 8a816a1fe3ea9e8608f99b0526245c8a1c07d688. Enumerate only safe residues by CRT lifts, not all P phases. Sort the safe positions, compute exact integer gaps and no-barrier counts, and compute N_R(x) for every starting residue by an event sweep: N_R(x+1)-N_R(x)=f(x+R)-f(x). At a barrier b the two change locations are b-R+1 and b+1 mod P; aggregate equal locations. Each interval between changes has constant count, so its multiplicity is known exactly. Check total count P R delta and equality of no-barrier count with the cyclic gap formula. Compute variance, discrepancy, and Fourier coefficients with floating-point arithmetic and small tolerances; no claim of exact real-number computation. Check the explicit Fourier bounds, max-gap bound, and integrated forward mean for each period. Y=5,7,11,13,17,19,23,29. Test R=1, ceil(1/delta), ceil(4/delta), ceil(16/delta), ceil(P beta), ceil(2P beta), floor(P/2), P (clamp to [1,P], deduplicate). No actual MIN trajectory replay or Lean compilation in this turn.

At Y=29: P=111546435, b=142560. Mean consecutive gap782.4525463, maximum5355, mean forward distance668.1765301, all in half-horizon units. Thus actual horizon mean gap1564.9050926, maximum10710, mean forward1336.3530602. For R3130, no-barrier fraction .0014526058138926627, exact interval count relative variance (numerical evaluation) .12983683740359764; for R12520 no empty interval. At Y23 mean gap374.2164352, max1785, mean forward316.8985108. At Y19 mean gap177.2604167, max714, mean forward143.7998942. All checks pass. The analytic upper bound is still very loose in these windows: at Y29, 2P beta=3653071.3960, maximum gap bound40372618.9899, mean forward bound16142457.3516. In particular these tests demonstrate the exact counting method and gap distribution, not that the analytic estimates are close to observed values. No extrapolation of the finite max-gap/mean-gap ratios.

## 7. Next target

The geometric route has now yielded a uniform Fourier bound, including the maximum gap and forward distribution, and an explicit scale obstruction. Bounding the full LOW peak by the next universal barrier cannot close the required coefficient; further progress requires the clock-selected paths (signed gain and terminal/restart distribution) rather than an improved density estimate for the permissive barrier set alone. The global physical far-coalescence estimate also remains unresolved. No main edit, no new branch, no twin-prime proof.
