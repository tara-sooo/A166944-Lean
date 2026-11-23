# Twin-prime-first new idea: top-prime-band exclusivity and growth-spectrum collision sieve

Date: 2026-11-23 JST. Research brainstorming/diagnostic, not a proof of an unbounded q-return estimate, twin-prime infinitude, or full A166944. Uses the verified finite LOW7 wheel (time<=56, growth<=106) from draft PR #5, GitHub Actions successful run 45130164879.

## 1. NEW deterministic large-band non-coincidence lemma (paper)

As previously established for the exact FINAL squarefree clipped parity-GCD wheel, every clipped nonunit event increment d at n<=K satisfies d<=n/2 if n is even, and d< n/3 if n odd. The latter uses the exact odd quotient >=3. For dyadic X, M<2X and K=floor((7M-1)/4)<7X/2, so d<K/2<7X/4. Let B=ceil(sqrt(7X)); B^2>=7X. Therefore

    d < 7X/4 <= B^2/4.

If two distinct prime factors q,r of d both satisfied q,r>=B/2, their product qr>=B^2/4>d, impossible. Hence:

    EACH EVENT HAS AT MOST ONE PRIME FACTOR q>=B/2.   (TOP-EXCLUSIVE)

This is an unconditional elementary paper deduction about a SINGLE clipped event, not an upper bound on repeated occurrence of the same large q. In particular the high-band event label is unambiguous; it is not affected by simultaneous factors from lower bands.

## 2. Original-GCD event-jump empirical bands

See independently written compact full original-parity-GCD event-jump scanner
research/high_band_return_audit.cpp (strict C++17). It counts ALL incidences q|d for q>=11, even if q is masked by a smaller prime. Bands: 0:11<=q<B/4; 1:B/4<=q<B/2; 2:B/2<=q<=B, with real inequalities rather than rounded band endpoints.

X     B     returns band 0  returns band 1  returns band 2  all-q returns
4096  170        1984             39              11           2034
16384 339       17677             32               8          17717
65536 678       83908            168               0          84076
262144 1355    499253            535               0         499788

For X262144, the top half band has 7,850 prime-label incidences, ALL first uses, with zero repeated q in that band. This is a finite observation and NOT the assertion that repeated q>=B/2 is impossible for arbitrarily large X. No such asymptotic theorem has been established. The mid band q in [B/4,B/2) has 535 repeats, and the overwhelming majority are below B/4.

The existing research/low7_one_donor_reuse_scan.cpp showed same (M,q,r) donor pairs can recur 2 or 3 times. That refutes pair-label injectivity, not TOP-EXCLUSIVE, since the latter concerns simultaneity in one event.

## 3. Replace individual q-hit process by a band-label collision process

Partition primes q in [11,B] into O(log B) geometric bands J_i. For a source M and band J, list all full-wheel events carrying a q in J, giving q labels. In the top J=[B/2,B], TOP-EXCLUSIVE ensures each band event has EXACTLY ONE label q, even with lower-prime simultaneous factors.

Let N_q(M) be the number of all q-bearing events, and define

    R_J(X) = sum_(M in I_X) sum_(q in J) (N_q(M)-1)_+.

The EXACT identity is R_J=sum_M (# total J-label incidences - # distinct J labels). Hence it is a repeated-label COLLISION statistic on a time-ordered source-selected word, independent of whether the labels are minimum owners.

For any band, (N_q-1)_+ <= binom(N_q,2), so it would suffice to control the source-averaged band-collision second factorial moment, without enumerating donor pairs (q,r) or incorrectly asserting uniqueness across repeated excursions.

A concrete strong but OPEN sufficient input for twin infinitude is, uniformly over O(log B) dyadic bands J,

    R_J(X) <= C * X * B / (log B)^2.

Summing bands gives R_ALL=O(XB/log B)=o(XB), which dominates the actual minimum-high-owner R7 and contradicts the earlier no-twin lower bound R7 >=(9/224-o(1))*XB. This condition is NOT proved. It is different from, and need not follow from, the previously proposed uniform per-q O(X) target; it asks for additional band-averaged cancellation in large bands.

## 4. Handle many high donors at once by an additive growth spectrum, NOT pair-by-pair

Fix two consecutive actual q-bearing events, with q>=11, and let there be m intervening clipped non-q events carrying a factor >=11, with increments d_1,...,d_m. All remaining events are LOW7-supported, forming m+1 partial blocks. From the LOW7 finite certificate, the cumulative even LOW7 growth A satisfies 0<=A<=106*(m+1). The total q-free recharge is

    E = sum_(j=1..m)(d_j-1) + A.

The exact q-post-hit congruence forces

    q divides (E-1) OR (E+1) OR (E-3).   (GROWTH-SPECTRUM)

This simultaneously covers zero, one, two and arbitrarily many foreign-high-donor events, including composite donors, regardless of their size and repeated pair labels. With m=1, d_1=r prime, it specializes to the earlier finite-shift q/r upper-sieve relation. With many donors it converts the problem into source-conditioned distribution of SUMS of actual donor growth modulo q.

A proposed concrete attack uses Fourier orthogonality:
  # {selected cumulative gains E: E=c mod q} =
    (1/q) sum_(a=0..q-1) exp(-2pi*i*a*c/q) * sum_(selected E) exp(2pi*i*a*E/q).

Condition on the actual post-q states and the finite LOW7 residue type, then seek cancellation in nonzero frequencies across the DYADIC SOURCE ensemble. This does NOT assume q-free shadow states are uniform or independent, and finite LOW7 automaton gives an explicit finite list of possible low-block corrections. Proving a sufficient source-weighted exponential-sum estimate is the genuine OPEN ingredient; the Fourier identity alone gives no saving.

## 5. Specific discriminating next test

Instrument the same exact-GCD scanner by q/B band and by intervening high donor count m=0,1,2,3,>=4, and compute the *selected* Fourier coefficients of recharge E modulo each q after q-hit. Check whether higher bands have a measurable spectral gap/discrepancy saving after low-residue-state conditioning, rather than testing only total returns. The existing all-q donor scanner at X16384 shows multi-donor returns dominate; an argument restricted to one donor cannot finish the proof.

If the source-conditioned Fourier cancellation fails for specific q or phases, isolate the exceptional states and charge them with an explicit finite-state potential instead of postulating uniform CRT equidistribution. A two-scale iteration (top band then lower bands) must NOT transfer final-wheel q counts by falsely assuming monotonicity in prime insertion: the documented disappearing-hit counterexamples show that transfer is invalid without a comparison theorem.

Only TOP-EXCLUSIVE, the algebraic GROWTH-SPECTRUM inclusion, and the reduction from the explicit bandwise return hypothesis to twin infinitude are currently paper deductions; the dyadic source-selected Fourier estimate, asymptotic returns and twin infinitude remain OPEN.
