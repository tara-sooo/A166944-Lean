# Prime-root full-horizon energy: eliminate injected-root mergers and extend the near-origin bound

2026-11-25 JST. Continues 69b2e35def3d0843880822d1ec911862c1dd2f9c, using the source ledger at 9450ea5e3ebd0909bffb775093330e2d37cd968e and full-horizon clock/sieve bound at 73458de887def94d00eeaf2d2d3b9c59a44b8137. This is an alternative restricted-source route for twin-prime infinitude, not a bound on the original full-source energy. New paper deductions and exact finite audit; the asymptotic late-energy estimate remains OPEN, no new Lean compilation.

## 1. A source family with no incoming edge at any injected root

Take dyadic X sufficiently large, B=ceil(sqrt(7X)), and use ONLY prime original roots

    P_X = { M prime : X <= M < 2X }, N_P=|P_X|.

Keep EXACTLY the same canonical MIN state t0=M+2, C0=2M-2 and original cutoff K(M)=floor((7M-1)/4). No change to the selected prime pool p<=B or the clock competition. Restricting the source ensemble does not change any individual trajectory.

If an incoming event reaches an injected prime root, its time is odd, t=M+2. The odd MIN clock requires t=p+2 mod 2p, so p divides M. But M>=X>B>=p; contradiction to primality of M. Thus every such root has indegree zero even in the full original physical graph. ROOT demotions vanish identically in the prime-source representative ledger.

Important distinction: composite roots of the original full ensemble may still be visited by one or several prime-source trajectories. They are NOT injected roots in the restricted ensemble, and meetings there are accounted for by SAME or distinct-label demotions. The argument does not exclude such physical meetings or their shared suffix masses.

## 2. Exact clock threshold at the reduced source density

Write W_P(C)=number of prime original tags visiting pre-event horizon C, R_P=sum_C r(C) W_P(C), E_P=sum_C r(C) W_P(C)^2, with r(C) the minimum eligible prime or zero. Use S0=sum_C r(C) over the full horizon range. The existing deterministic inequalities imply R_P=O(X N_P), and if every prime source ends at a non-twin terminal, then

    2 R_P >= H_P - 2 B N_P,  H_P=sum_{M in P_X} (K(M)-(M+2)).

The prime number theorem and partial summation give

    N_P ~ X/log X,
    sum_{M in P_X} M ~ 3 X^2/(2 log X),
    H_P = (9/8+o(1)) X N_P.

Here K(M)-(M+2)=3M/4+O(1). Hence under the no-twin hypothesis,

    R_P >= (9/16-o(1)) X N_P
        = (9/32-o(1)) X^2/log B.                         (1)

For a finite window with H_P>2BN_P, the EXACT certificate

    4 S0 E_P < (H_P-2BN_P)^2                              (2)

is sufficient, by Cauchy R_P^2<=S0 E_P. It needs no asymptotic estimate.

The established upper-bound sieve gives S0=O(X B/log^2 B). Since B^2=Theta(X), the new sufficient asymptotic target is

    E_P=o(X^2 B)                                         (3)

along an unbounded dyadic subsequence. This is a stronger absolute scale than the full-source target O(X^2 B log B), reflecting the smaller source population. It is not a logical consequence of the old open full-source bound, nor is the latter a consequence of (3). A constant-threshold version directly uses (2). The terminal smaller prime is >=2X-1 (initial C>=2X), so successful windows unbounded imply infinitely many distinct twin pairs.

## 3. Unconditional longer near-origin removal

For a gain radius T, let W_P,late(C) count only prime tags with C-(2M-2)>T. For a fixed horizon C the number a of remaining near-origin prime roots is bounded by the number of primes in an interval of length <=T/2+1. The standard uniform interval upper bound pi(v+h)-pi(v)=O(h/log h) for h>=3 (e.g. Brun--Titchmarsh with modulus 1) yields a=O(T/log T), uniformly in C for growing T. If b=W_P,late, then (a+b)^2-b^2<=2a(a+b). Therefore

    E_P - E_P,late <= O(T/log T) R_P.                    (4)

The estimate uses original tags even after arbitrary physical coalescence. It is not a bound on the number of possible physical states.

In particular take T=floor(B log^(2-epsilon) B) with fixed 0<epsilon<2. Since R_P=O(X^2/log B),

    E_P - E_P,late = O(X^2 B/log^epsilon B) = o(X^2 B).

Thus (3) reduces to E_P,late=o(X^2 B), with BOTH source horizons more than T above their own origins. This removes all near-origin overlaps at a larger gain radius than the previous B log B full-source reduction. The same reasoning applies to any trimmed source-event incidence measure bounded by W_P. For near root separations <=d, each prime root has O(d/log d) other prime roots; the total ordered weighted pair energy is O(d/log d * R_P), with the diagonal O(R_P). This does not assume either independent arrivals or contiguous source fibres.

## 4. Adapt prior unconditional ledger removals to the prime-source scale

Use the same maximal-cutoff representative bookkeeping. There are at most N_P demotions, at most one per tag, each with total suffix r cost O(X). Restricting the source family preserves the deterministic graph/representative argument. ROOT=0; remaining categories are SAME, BIG, MIXED, and the representative's own events.

Set Q=ceil(B/log^(1/8) B), A=floor(log^(1/8) B), z=max(1,floor(log^(1/8) B)).
- BIG: distinct incoming primes p,q>=Q require p,q to divide t,C (even) or t-2,C+2 (odd). The previous CRT bound O(X^2/(Q^2 log^2 Q))=O(X/log^(7/4) B) counts physical vertices. At most two such labels per vertex eventually since Q^3>7X+2. Hence the suffix cost of the newly demoted representatives is o(X^2/log B).
- SAME with lag <2z and both histories recent-large within gain A: the theorem at 69b2e35 bounds distinct physical predecessor pairs by O((A+1)^2(z+A+1) X^2/(Q^2 log^2 Q))=O(X/log^(11/8) B). The scale gate Q>2z+3A+2 holds eventually. Each marked demotion injects into these pairs, so its tag suffix cost summed over marked SAME is o(X^2/log B).
- Surviving representative events with selected label >=y=ceil(sqrt B): by the previous representative-high arithmetic sieve bound O(XB+X^2/log^2 y)=o(X^2/log B). The XB term accounts for events whose representative is demoted at the target; in the restricted ensemble it may even be replaced by O(N_P B).

These remove only disjoint event/tag contributions, not the cost of all previously demoted tags arriving at a marked vertex. Let W_rem be the remaining prime-source incidence measure and R_rem its r budget. Then R_P-R_rem=o(X^2/log B). By (1), Cauchy, and (4) applied to W_rem, a proof of

    sum_C r(C) W_rem,late(C)^2 = o(X^2 B)

would still imply twin infinitude. The dominant residual categories are SAME with small-label histories, MIXED, and representative-low. Composite reset-line meetings are included in these classes, not silently removed. The original source-weighted far-coalescence problem is still open.

## 5. Actual finite audit

Standalone ECMAScript research/min_prime_root_energy_audit.mjs. Exact source readback at b56da429c3de85428a18425d05c8de79dc2c9353, blob 6b449e34dddd83e1c05bdcac6c25bb32214df97a. Run:

    node research/min_prime_root_energy_audit.mjs 256 1024 4096 16384 65536 262144

The audit function was executed in the available JS runtime (not a separate local Node invocation) at all six windows. It replays ALL original odd sources, separately collects prime-source incidence measures, checks literal parity GCD at small windows (6140 comparisons), horizon/time bound, all original-source post-event arrivals on the odd reset root line (must be composite roots), exact prime ledger with maximal-M incoming class representatives, disjoint demotion and suffix costs, and absence of incoming edges at prime injected roots. It checks the finite near-origin bound with the exact maximum prime interval count, both T=B and T=floor(B log^(3/2) B), and finite energy certificate (2) with BigInt cross-products. Integer-safety checks are included. The audit counts events rather than using a model for prime distribution.

| X | prime roots | prime events | R_P | E_P | E_P,late (T=B) | max W_P | certificate (2) |
|--:|--:|--:|--:|--:|--:|--:|:--|
|256|43|442|2948|17264|7900|12|no|
|1024|137|1102|8760|40448|7000|11|yes|
|4096|464|7094|77584|674854|201569|26|yes|
|16384|1612|32866|435124|5563300|1774855|47|yes|
|65536|5709|140255|2679611|42849045|11403743|67|yes|
|262144|20390|616116|16687054|361015358|98490131|108|yes|

At X=262144: B=1355, H_P=5996249986, S0=9566471, all-source events=3946588, all-source R=107745566 and E=14915941604. There were 286359 visits to original-window odd reset roots in the all-source audit; every arrival target was composite. Prime-source ledger: representative cost 4679586 (selected >=sqrt B cost 3681203), SAME suffix cost 10480003 (12908 demotions), BIG 0, MIXED suffix cost 1527465 (1890 demotions), ROOT 0. Of the actual SAME/MIXED demotions, 4054 occur on composite original-window reset roots, with suffix cost 3334454, illustrating why absence of ROOT does not imply absence of reset-line mergers. For T=floor(B log^(3/2) B)=26241, maximum prime-source gain is 9666, so late energy is zero in this finite window; the asymptotic hard regime is NOT exercised. T=B retains 98490131 late energy and is a nonvacuous finite diagnostic.

At X=256 one prime source ends non-twin; all other listed windows have zero non-twin prime sources. The direct finite checks do not establish (3), or a bound on how far future source trajectories travel.

## 6. Next proof task

This is a parallel source-family variant, not a replacement for the original full-source route. The main advantage is an exact removal of injected-root demotions and a uniform prime-density saving for near-origin/near-separation pairs. The cost is a stronger absolute energy threshold. The next mathematical target is a prime-source-weighted bound for late SAME and MIXED ancestry, including composite reset-line meetings; in particular compare the prime-source mass in reverse clock intervals with the full-source mass rather than assume it is smaller by log X. The previous exact reverse recurrence and cutoff-tagged cut transfer continue to apply by adding primality of the original root to the injection indicator. No proof of long-history prime-source dispersion or of the twin-prime conjecture; main untouched.
