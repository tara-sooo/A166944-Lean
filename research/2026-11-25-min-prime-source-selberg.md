# Prime-source weighted ancestry via a Selberg majorant and signed far-pair remainder

2026-11-25 JST. Continues 6d2f6bf9c38730703d431f574aecdf232bfed429 (prime-root energy) and the cutoff-tagged transfer at bcc8e73dcba8e7b0962012342cf5964b72e0909d. New exact deterministic sieve reduction, unconditional near-pair bound and finite audit. The asymptotic far-pair estimates and twin-prime conjecture remain OPEN. No new Lean compilation.

## 1. Use an explicit source sieve, not a prime-density assumption

Keep all canonical odd roots M in [X,2X), X dyadic, their original MIN trajectories and their individual K(M). B=ceil(sqrt(7X)). The r cost of each source is O(X) by telescoping gains. For any chosen subset of actual source-event incidences (for example, require C-(2M-2)>T), let I_M(C) be its zero-one indicator. Write W(C)=sum_M I_M(C), W_P(C)=sum_{M prime} I_M(C), E=sum_C r(C) W(C)^2, E_P likewise. Every estimate below works for these arbitrary retained incidences. No distribution of adaptive histories is assumed.

Choose an integer sieve cutoff D=floor(B^alpha), 0<alpha<=1/2 fixed, and define

    G=G(D)=sum_{d<=D, d odd} mu(d)^2/phi(d) = Theta(log D).
    G_d(Y)=sum_{k<=Y, k odd, gcd(k,d)=1} mu(k)^2/phi(k).
    lambda_d=mu(d) d/phi(d) G_d(D/d)/G  (odd squarefree d<=D),
    lambda_d=0 otherwise.

Then lambda_1=1, |lambda_d|<=1. The latter follows since every product e*k with e|d and k<=D/d coprime to d lies in G(D), and sum_{e|d}1/phi(e)=d/phi(d) for squarefree d. The standard order G=Theta(log D) follows, for example, by lower bounding with the harmonic sum of odd squarefree integers and upper bounding 1/phi(d) with its divisor expansion. Here and below all moduli in the sieve are odd.

For clarity the quadratic identity can be proved without appealing to an optimality theorem. Put y_k=sum_{k|d}lambda_d/d. Inversion of the definition gives y_k=mu(k)/(phi(k)G) for odd k<=D and zero otherwise. Since gcd(d,e)=sum_{k|d,k|e}phi(k),

    sum_{d,e} lambda_d lambda_e/[d,e]
       = sum_k phi(k)y_k^2=1/G=:c.

Define s(M)=(sum_{d|M}lambda_d)^2 >=0, delta(M)=s(M)-c. For M prime >D, s(M)=1, so s is a pointwise upper majorant of the prime-root indicator. For each odd l<=D^2, beta_l=sum_{[d,e]=l}lambda_d lambda_e; then s(M)=sum_l beta_l 1_{l|M}, sum_l beta_l/l=c, sum_l |beta_l|<=D^2.

At each C put A_l(C)=sum_{l|M} I_M(C), and

    Delta(C)=sum_l beta_l (A_l(C)-W(C)/l)
            =sum_M delta(M) I_M(C).
    W_s(C)=sum_M s(M) I_M(C)=c W(C)+Delta(C).

Thus W_P<=W_s pointwise. With the weighted norm ||f||_r^2=sum_C r(C) f(C)^2, let J=||Delta||_r^2 and E_s=||W_s||_r^2. Exactly

    E_P <= E_s = c^2 E + 2c <W,Delta>_r + J
               <= (c sqrt(E)+sqrt(J))^2.                 (1)

A one-sided refinement replaces J on the upper bound by ||Delta_+||_r^2, since W_P<=cW+Delta_+. No replacement of the ancestor mass by its expected prime density is made.

Since c=Theta(1/log B), sufficient asymptotic inputs on the same unbounded dyadic windows are

    E=o(X^2 B log^2 B),  J=o(X^2 B).                     (2)

They imply E_P=o(X^2 B), the sufficient prime-root criterion at 6d2f6bf. The raw energy target in (2) is weaker by a growing logarithmic factor than the earlier full-source sufficient O(X^2 B log B). This is conditional on the new residue discrepancy estimate; it does NOT establish either of the two inputs. Even the full-source energy target is still open. A finite certificate also follows by replacing E_P with the upper bound in (1) in 4 S0 E_P < (H_P-2BN_P)^2 when H_P>2BN_P.

## 2. Unconditional near-origin and near-separation removal for the signed sieve

For any consecutive interval I of odd root indices, cardinality n, the number with l|M is n/l+O(1), uniformly in its position, since l odd. Therefore

    sum_{M in I} s(M) = c n + O(D^2),
    sum_{M in I} |delta(M)| <= 2c n+O(D^2).              (3)

Also sum over the entire source window of s or |delta| is O(X/log B), because D^2<=B=O(sqrt X). With the O(X) bound on each source's complete cost, the weighted linear costs R_s=sum_C r W_s and R_abs=sum_C r sum_M |delta(M)|I_M(C) are both O(X^2/log B). The usual R=O(X^2) also holds.

Choose T=floor(B log^(2-epsilon) B), fixed 0<epsilon<2. The original prime-root near-origin lemma removed all incidences of gain <=T. Now (3) gives the same result for the NONNEGATIVE sieve majorant: the near-origin s mass at each C is <=O(T/log B+D^2), since the possible roots lie in a consecutive interval of length O(T). Writing W_s=a+b with a near and b late, a^2+2ab<=2a W_s. Consequently

    E_s(full)-E_s(late) <= O((T/log B+D^2) R_s)
                        = O(X^2 B/log^epsilon B + X^2 B/log B)
                        = o(X^2 B).                     (4)

The raw analogous difference is O(T R)=o(X^2 B log^2 B). For Delta, the near-origin vector itself has squared norm <=O((T/log B+D^2)R_abs)=o(X^2 B); therefore its addition/removal changes whether J=o(X^2 B), by the triangle inequality. Do not subtract signed near-origin squared norms as though the cross term were nonnegative.

For a pair of original tags define the retained overlap kernel

    K_T(M,M')=sum_C r(C) I_M(C) I_{M'}(C),

using late incidences C-(2M-2)>T if desired. This kernel is nonnegative and its row diagonal K_T(M,M) is O(X). The exact discrepancy energy is

    J=sum_{M,M'} delta(M)delta(M') K_T(M,M').

For ordered pairs with |M-M'|<=T (diagonal included), bound the ABSOLUTE sum. At any horizon, for fixed M, the nearby root weights |delta(M')| sum to at most O(T/log B+D^2) by (3), even after arbitrary coalescence or restrictions. Hence

    sum_{|M-M'|<=T} |delta(M)delta(M')| K_T(M,M')
        <= O((T/log B+D^2) R_abs) = o(X^2 B).            (5)

For raw energy the corresponding near-pair sum is <=O(T R)=o(X^2 B log^2 B). The result also applies with no late truncation. Thus after removing both near-origin incidences and near-separation pairs, the only remaining sufficient inputs are

    E_far = sum_{|M-M'|>T} K_T(M,M')
                  = o(X^2 B log^2 B),
    (J_far)_+ = max(0, sum_{|M-M'|>T} delta(M)delta(M') K_T(M,M'))
                  = o(X^2 B).                           (6)

The signed far-pair sum is NOT itself a squared norm; it can be negative. Only an upper bound on it is required. Equations (4),(5) are unconditional and require no uniformity of the ancestor sets. They eliminate short-range discrepancies at the correct prime-source scale. Equations (6) are open: the weighted arithmetic of long-range coalescence remains the difficult problem.

## 3. Exact signed cut transfer and an interval-run bound

In the binary source cut construction at bcc8e73, each left crossing entry e has original tags A_e. For any fixed weights w(M), including signed delta(M), use

    a_e^w(C,v)=sum_{M in A_e, K(M)>=v, C-(2M-2)>T} w(M).

Replay from e to its maximal original cutoff as before. With right weighted late occupation W_R^w(C)=sum_right w(M) I_M(C), the cross-cut sum is exactly sum_e sum_{(C,v) in replay} r(C) a_e^w(C,v) W_R^w(C). If additionally requiring |M-M'|>T, impose this pair predicate INSIDE the product (or subtract the exactly counted near-pair term). Summing unfiltered signed cross-cuts and subtracting near pairs gives J_far. No sign or independence assumption is needed. Previously demoted tags retain their original weights.

For a fixed horizon let k(C) be the number of maximal consecutive runs of retained odd root indices {M:I_M(C)=1}. From the exact interval discrepancy in (3) one also has |Delta(C)|<=D^2 k(C) (with an absolute constant). Hence J<=O(D^4 sum_C r(C) k(C)^2). This is a second, potentially useful sufficient control in terms of fragmentation of the reverse ancestry set, not an established bound on fragmentation. The direct signed cut route avoids the loss D^4 and is the preferred next target.

## 4. Actual finite audit

Standalone ECMAScript research/min_prime_source_selberg_audit.mjs, read back exactly at f9f1dc7420a32c11fe0c4bd689fc12acfbb7c723, blob e41ba198434aa887de806426efc618a4d4c2105b. Run from repository root:

    node research/min_prime_source_selberg_audit.mjs 256 1024 4096 16384 65536 262144

Executed the actual audit function in the available JS runtime at all six windows, not a separate Node invocation. All original sources replayed with their own cutoff; 6140 literal per-tick parity GCD comparisons. Three D choices floor(sqrt B), floor(B^0.75), floor(B/2) (last two exploratory, outside the unconditional near bound's asymptotic choice). Checks lambda bound, quadratic identity, prime majorant pointwise, exact expansion and upper bound (1), signed near and absolute near bound by exact maximum local weight. Full, late B, and late floor(B log^1.5 B) measures are computed. For late B the near source-separation sum uses a sliding root window, evicts expired original tags by exact replay, and counts both orders plus the diagonal. The far signed term is the total squared discrepancy minus this near signed contribution. Floating-point sieve weights and energy computations checked with numerical tolerances; no exact rational arithmetic or Lean compilation.

Table uses D=floor(sqrt B), late gain radius B and pair separation cutoff B, not the asymptotic T. Rounded values for signed sums.

| X | D | E_late | E_P,late | c^2 E_late | J_late | J_far |
|--:|--:|--:|--:|--:|--:|--:|
|256|6|69034|7900|22542|178|-91|
|1024|9|141838|7000|38610|2533|206|
|4096|13|4044179|201569|917047|12385|-405|
|16384|18|40569092|1774855|7753059|37176|-856|
|65536|26|370428029|11403743|60626420|369905|2605|
|262144|36|4052570879|98490131|584756173|2494247|-16457|

At X=262144, B=1355, all 3946588 original events, 616116 prime-source events, 20390 prime roots. For D=36, G=2.6325577201, E_far=232640038, J_near_signed=2510704, J_near_absolute=570034961, J_far=-16457, E_s,late=591428122. The full-energy values are E=14915941604, E_P=361015358, J=9897659, E_s=2173604253. The diagnostic D=677 gives J_far=-46968, E_s,late=241273809, J_late=1979217. These signed cancellations are finite observations, not uniform bounds. Every tested window had zero late incidences at T=floor(B log^1.5 B), so that asymptotic regime was NOT exercised. The B-scale tests are nonvacuous but still far from the hypothesized long-trajectory regime.

## 5. Next task

The new sieve majorant avoids attempting to count primes in an arbitrary adaptive reverse fibre by dividing by log X. All unknowns are now ordinary all-root overlap kernels and their explicit signed residue correlations. The priority is to bound coarse-level cross-cut signed mass using the exact cutoff-tagged transfer (or prove a useful estimate of ancestry fragmentation). A separate raw far-pair bound at the weaker scale in (6) is still needed. The finite cancellation does not establish either of those estimates. Main untouched; no proof of twin infinitude.
