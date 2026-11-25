# Same-label quotient sieve and unconditional removal of low-clock blocks

2026-11-25 JST. Continuation of 11104dcf1596d950fc44438e89d05f224aa6db13 on research/min-prime-root-repeat-energy-2026-11-25. Paper deductions with a self-contained two-form upper-bound sieve derivation (standard Mertens and elementary prime-sum bounds used). Actual integer MIN trajectories, not the CRT ghost. No Lean compilation, no novelty assertion, twin-prime infinitude OPEN.

## 1. The quotient at repeated selections of one prime

Keep the canonical prime-root ensemble with odd prime M in [X,2X), N such roots, B=ceil(sqrt(7X)), original root cutoff K(M), even pre-event horizon C, selected prime p, and sign sigma in {-1,1} such that p divides C+sigma. As before, r(C) is the least odd prime <=B dividing either C-1 or C+1, so r(C)<=p. The actual next wait is <=2r(C). Write G_M for the total horizon gain of source M. The invariant gives G_M=O(X), uniformly; sum of all selected primes is <=1.5 sum G_M=O(XN).

For each original selected occurrence of p>=5 define its integer quotient coordinate
    a=(C+sigma)/p=2n+1.
Both numerator and p are odd; a is positive odd. For successive occurrences of p, if S is the pre-horizon increase, then S+sigma_next-sigma_old is a positive even multiple of p, by the existing recharge identity. Hence n strictly increases along this original same-label list. In particular there is no repeated n within a source and p, regardless of all intervening donor labels, times, or mergers.

For a block of b consecutive ORIGINAL hits of p, let H=n_last-n_first+1. Then H>=b and the gain span is exactly
    S_block = 2p(H-1) + sigma_first - sigma_last.
The half-open gain spans of disjoint blocks of this label are disjoint, even if their donor intervals overlap spans for other labels. Their lengths sum to <=G_M.

Let 3<=z<p, with z<=B. The condition r(C)>z is EXACTLY the simultaneous absence of odd prime factors q<=z in
    2n+1,  p(2n+1)-2sigma.
Indeed C+sigma=p(2n+1), C-sigma=p(2n+1)-2sigma, and p>z. For fixed sigma each odd q<=z excludes precisely TWO distinct n residues modulo q, because q does not divide 2p and the offsets differ by 2sigma. This is a different use of arithmetic from the previous CRT return-transcript count: it concerns actual expensive clock hits, not the probability of selecting a label. The sign is allowed to change arbitrarily across occurrences. Count the union of the two fixed-sign sifted sets to allow that.

For reference, with P_z=product_{3<=q<=z}q and rho_z=product(1-2/q), the exact number of admissible residues for either fixed sign over a complete period is P_z rho_z. Over any interval of H consecutive integers the union count is at most
    min(H, 2 P_z rho_z (floor(H/P_z)+1)).
This elementary CRT bound is useful at finite scales; the full period can be too large for the asymptotic short block, so we instead use the following sieve.

## 2. Uniform two-form bound without any dependence on the selected prime's size

Claim: uniformly in p>z, either sign, and an interval of H consecutive n integers,
    #{n: both forms have no odd prime factor <=z}
       << H/(log z)^2 + z^6 .
Here and below absolute constants may be enlarged at bounded z. In contrast to the previous affine-prime-pair sieve, the coefficients can be as large as B: there is no loss for their prime factors because the leading coefficient's only odd prime divisor is p>z and the determinant has no odd prime divisor.

Derivation by Selberg's quadratic majorant. Let d range over squarefree positive integers d<=z built from odd primes <=z (including 1). For every squarefree such modulus, the number of n for which each q|d divides the product of the two forms is
    H g(d) + O(2^omega(d)), g(d)=prod_{q|d} 2/q.
The error constant is absolute by CRT, since there are exactly 2^omega(d) residue classes modulo d. This also holds for lcm(d,e) with d,e<=z, although it can exceed z.

Write h(d)=prod_{q|d}(q-2)/2, G(z)=sum_{d<=z}1/h(d), over the allowed d. With real weights lambda_d supported there and lambda_1=1, the square of sum lambda_d over d dividing the product is a nonnegative majorant of the sifted indicator (on a survivor only d=1 contributes). The main quadratic form diagonalizes exactly:
    sum_{d,e}lambda_d lambda_e g(lcm(d,e))
       = sum_l h(l) Y_l^2,
    Y_l=sum_{l|d}lambda_d g(d).
This uses 1/g(k)=sum_{l|k}h(l). The set of supported d is divisor-closed. Möbius inversion gives lambda_1=sum_l mu(l)Y_l. Set
    Y_l=mu(l)/(h(l)G(z)).
Inverting yields admissible lambda_d with main form 1/G(z) and
    |lambda_d| <= 1/(h(d)g(d))
                = prod_{q|d}(1-2/q)^(-1) <= d.
For clarity, the exact inverted numerator is mu(d)/(h(d)G(z)) times sum of 1/h(m) over allowed m<=z/d coprime to d, and the latter sum is <=G(z). Thus the displayed bound follows even at q=3.

Elementary lower bound G(z)>>log^2 z: take w=z^c for a sufficiently small absolute constant c>0. Over all squarefree products of odd q<=w, assign mass proportional to 1/h(d). The total mass is prod_{3<=q<=w}(1-2/q)^(-1)>>log^2 w by Mertens (the ratio to the square of the ordinary Euler product converges to a nonzero constant). Under its normalized product weights, the probability q is included equals 2/q. Therefore the expected log d is sum_{q<=w}2 log(q)/q=O(log w), by the elementary Chebyshev/partial summation bound. Choose c small enough that this is <=(1/2)log z. By Markov at least half the mass lies at d<=z, and these terms belong to G(z). This proves the lower bound. The probability here is only a convenient proof of an elementary finite Euler-product mass inequality, NOT a random model of the MIN trajectories.

The error in the majorant sum is at most
    sum_{d,e<=z}|lambda_d lambda_e| 2^omega(lcm(d,e))
       <= sum_{d,e<=z} d^2 e^2 = O(z^6).
Together these prove the claim. Neither the phase of the interval nor the source root is assumed random. Taking a union over both signs adds only a factor two. This proof does not require an external sieve theorem or independence of any histories.

In a b-hit block take z<=b^(1/16). Since H>=b, z^6<=b^(3/8)=o(H/log^2 z), uniformly for 3<=z<=b^(1/16). Distinct quotient coordinates then give
    # {actual expensive hits r(C)>z in block} << H/log^2 z.
For the actual clock sum R_block of this label's b hits,
    R_block <= z b + (p-z) #expensive
            <= z b + C0 p H/log^2 z
for an absolute C0. Here the block consists of successive p-hits, not a contiguous all-label segment: no bounds on the number or sizes of donors are necessary.

## 3. New unconditional block deletion at a growing mean-span scale

Set l=loglog B, b=floor((log B)^(1/4)), Y=ceil(l) for sufficiently large B. Use p>=Y (so p>=5 eventually); the finite code guards small values. For each such prime define
    z_p=floor(min(sqrt(p),b^(1/16))),
    eta_p=(log z_p)^(-1/2).
Then z_p>=3 eventually, z_p<p, z_p/p<=1/sqrt(p), and log z_p>>log l uniformly for p>=Y (since b grows much faster than l). In particular eta_p tends uniformly to zero and z_p/p=o(eta_p).

In every original source's complete p-hit list, partition from its END into disjoint consecutive blocks of b hits, leaving a first incomplete prefix of fewer than b hits. This convention ensures the remainder is among the earlier fixed k=floor(sqrt(log B)) baseline hits; even independently its total selected weight across sources is at most N b sum_{p<=B}p=o(XN). Mark it. For every complete block mark all b hits if its original total r cost satisfies
    R_block <= eta_p p b.
The sum of costs of all such blocks is bounded by max_{p>=Y} eta_p times the total selected weight O(XN), hence
    R_low-block=O(XN/sqrt(log l))=o(XN).
Finally mark any remaining p>=Y hit with r(C)<=z_p. Its total r cost is O(XN/sqrt Y)=o(XN), since r(C)/p<=z_p/p. These are CLOCK-cost deletions: their selected-prime weights need not be small. Do not add them to a seed used in selected-weight donor propagation, gain halos, or same-label dilation. They may be intersected with all preceding deletions without changing actual trajectories.

Every block not marked by its cost has
    eta_p p b < R_block <= z_p b + C0 p H/log^2 z_p.
Thus, uniformly for sufficiently large B,
    H >= c0 b (log z_p)^(3/2)
with an absolute c0>0. In gain coordinates this implies
    S_block >= c1 p b (log z_p)^(3/2).
Hence **every remaining p>=Y hit must belong to a long-mean-span block and must be individually expensive (r(C)>z_p)**. In particular any family of b-hit blocks of bounded normalized mean span H/b, or H/b=o((log z_p)^(3/2)) uniformly, lies in the cheap-block class eventually. One can also delete all blocks H<=b(log z_p)^(3/2) at O(XN/sqrt(log l)) clock cost by the upper bound even without calibrating c0. No claim that the finite diagnostic constant K=3 in the audit implies cheapness at small B.

The new scale reaches a power of loglog B for p large enough that z_p=b^(1/16), much larger than the previous short individual return parameter K~(logloglog B)^(1/4). This removes short-average return episodes even when their intermediate high-label words are sparse, contain arbitrary donor sizes, or do not meet the dense-word background/comparability assumptions. It does not remove a long-mean block just because one of its individual returns is short. It is legitimate to use the full list instead of a clean-episode partition: the previous dilation and other marks are retained, and every remaining event is tested against its original block before any deletion.

## 4. Deterministic residual multiplicity bound and the hybrid

For any fixed source and p>=Y, let n_new(M,p) be the number of hits surviving all deletions including the new ones. Each retained complete block contains at most b such hits, and each has span >=c1 p b(log z_p)^(3/2). The block spans for this fixed label are disjoint. Therefore
    n_new(M,p) <= C1 G_M/[p(log z_p)^(3/2)].
The bound is valid even if the surviving hits in that block are separated by previously marked hits. In addition to the old adaptive occurrence cap and clean preceding t label hits, this imposes an unconditional multiplicity/average-span restriction without any deleted-prime shadow mixing hypothesis. For example on p>=Y the part of the medium second moment satisfies the exact consequence
    sum_{M,Y<=p<Q} n_new(M,p)^2
       <= C1 sum_{M,Y<=p<Q} [G_M/(p(log z_p)^(3/2))] n_new(M,p).
This can be used to turn the remaining medium moment into a suitably weighted first-moment bound. It is not itself the desired O(NB log^3 B) estimate. Primes y<p<Y remain subject to the earlier clean-episode and adaptive-cap restrictions, not the new quotient sieve deletion.

The extra LOW absorption cost is also negligible, despite the new deletions being r-cost only. ALL events with p>=Y number O(XN/Y) by disjoint gain and p-1>=Y-1. With previous LOW primorial L<=(loglog B)^(1/4) we have L/Y=o(1), so the LOW charge for all newly deleted events is O(LXN/Y)=o(XN). The previous selected-weight halo bound, relaxed light-horizon r-cost bound and their separate LOW accounting are unchanged.

Consequently the preceding joint OPEN criterion still applies to the smaller original-tag incidence sets:
    Z_m=sum_{M,y<p<Q} n_new(M,p)^2=O(N B log^3 B),
    E_h,late=sum_C r(C) W_new,late(C)^2=o(X^2 B)
on the SAME unbounded dyadic windows, with Q=ceil(B/log B) and near-origin radius as before. Or use the previous intermediate-defect/tail alternative for the high part. It gives R=o(XN) and the earlier clock contradiction to no twins. The new deletion is unconditional, but neither residual asymptotic bound is established. It avoids trying to treat cheap-clock selected weights as negligible gain or transferring an independent ghost probability to actual prime sources.

## 5. Exact finite audit and independent sieve oracle

Standalone ECMAScript research/min_prime_root_quotient_blocks_audit.mjs, exact remote readback at 171b9a498068fc7457ea6d398412eca8f226527d, blob 353dc8eaef64be72b0973862c13ef22052702305. Reproduce:
    node research/min_prime_root_quotient_blocks_audit.mjs 256 1024 4096 16384 65536 262144
Executed the audit function in the available ECMAScript runtime, not a separate Node executable. Three modes x six windows, all actual prime roots and original cutoffs; 1724 literal parity-GCD comparisons per mode at X256/1024. Checks exact quotient divisibility/strict increase, exact span identity, disjoint same-label block spans, equivalence of actual expensive r(C)>z with the two-form roughness for every tested block hit, full CRT period product and exact union count over each quotient interval, clock charge z b+(p-z)#expensive, disjoint cost partition and original source energy (BigInt). It deliberately tests this block deletion by itself, not the entire cumulative adaptive/halo deletion (which previously made most finite residuals empty).

Independent Selberg oracle verifies the quadratic-form identity, weights <=d and pointwise survivor majorant for z=3,5,7,11,17,31,61,101 and selected primes >z, both signs, multiple interval starts/lengths. 32 systems, 192 intervals, 4536 survivor majorant checks, 103 weight-bound checks; max floating-point main identity error 3.75e-16. The finite arithmetic of the CRT and MIN checks is integer-exact; the Selberg oracle uses floating-point tolerances. The lower asymptotic G(z) bound and uniform asymptotic estimate are paper deductions, not measured limiting laws.

Analytic mode uses finite guards b>=2 and z>=2 (in these samples b=2,z=2,eta=1), so every full block is marked by the trivial r<=p bound; this is a vacuous check of the asymptotic mean-span gate. Two nonvacuous diagnostics: wide b=3,Y=7,z=3,eta=1/2,K=3; fixed b=6,Y=17,z=5,eta=1/2,K=3. Both deliberately retain many costly compact blocks at finite parameters. The diagnostic compact flag H<=Kb is a measurement, not an unconditional finite deletion rule.

| X | wide full blocks | wide costly blocks | wide expensive hits (all blocks) | wide residual clock p>=7 | fixed residual clock p>=17 |
|--:|--:|--:|--:|--:|--:|
|256|10|10|30|304|0|
|1024|10|9|26|195|0|
|4096|275|274|733|6689|0|
|16384|1556|1534|4130|39347|401|
|65536|7111|6871|18881|175404|4178|
|262144|35596|34537|94406|971239|35315|

At X262144 N=20390, events616116, original R16687054, gain19169594, matching prior audits. Wide mode checks106788 block hits, 35596 exact interval capacity counts; 7350 compact blocks, including 7252 costly ones; 1059 low-cost blocks total. Prefix cost14460004, low-block cost26725, individual cheap hits inside costly blocks cost33438, surviving p>=7 clock971239 and 92465 hits, Z490265 (all p>=7, NOT the final medium moment). Unchanged p<7 clock1195648. Fixed mode: 419 complete blocks, 413 costly, 6 cheap; 2514 block-hit checks, 2125 expensive; cost prefix14390256, low-block324, individual cheap1549, retained35315 and 2107 hits, Z10939 (all p>=17); unchanged p<17 clock2259610. High residue p>=Q=188 happens to be empty in both modes at this largest scale, but the full no-twin asymptotic regime is not sampled. All exact assertions passed. No Lean compilation.

## 6. Next target

Rather than treating every repeated p as equally costly, the new residual is concentrated on blocks with a large quotient span and many actual rough quotient hits, as well as on the small band y<p<Y. Next investigate actual p-deleted-shadow returns to the two-form rough lattice and a weighted count of long-mean blocks by origin, possibly combining the previous actual-source energy and the inverse complexity/Kraft ideas from the parallel short-clock branch. The block proof uses only genuine MIN selections, not a new model. The asymptotic residual estimates and twin conjecture remain OPEN. Main and other branches untouched.
