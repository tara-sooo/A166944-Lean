# A166944: review of prime-power wheel insertion and signed growth coupling

Date 2026-11-22 JST. **Assessment:** mathematically meaningful route to the existing dyadic mean-growth criterion, with exact first-divergence arithmetic and genuine cancellations. Global average bound, Cap B, twin-prime infinitude **NOT PROVED**. No new Lean kernel compilation.

## Source and independent checks

The supplied user archive \`A166944-Lean.zip\` contains:
- \`mission_scan/twin_proof/cap_bound/wheel_insertion_idea.md\`
- \`mission_scan/twin_proof/cap_bound/wheel_insertion_audit.py\`
- \`mission_scan/twin_proof/cap_bound/WheelCheckpoint.lean\`
- \`mission_scan/twin_proof/cap_bound/refire_source_audit.md\`
- \`mission_scan/twin_proof/cap_bound/refire_independent_audit.md\`.

The Python audit was **executed from the ZIP byte content** and passed: 41,034 wheel-pair checks, 914 complete-lift residue-class experiments, and the cited X=256 signed decomposition. The Lean file **contains** proofs of \`even_barrier\` and \`insertion_iff\` and prints their axioms; a Lean toolchain was not present in this assessment runtime, so its claimed successful mission-environment build was **not rerun**. The exact \`2/p\` full-lift count and the global signed mean are NOT part of these two kernel theorems.

## 1. Exact first divergence and the necessary qualification

For odd initial M≥7, fixed cutoff T, and an odd wheel L, compare \`e_L(n)=gcd(h(n,C_L),L)\` and \`e_{Lp}(n)=gcd(h(n,C_{Lp}),Lp)\` under the ORIGINAL parity gcd. Put \`q=p^(v_p(L)+1)\`. While paths are identical, the newly available factor changes the gcd iff \`q|h\`; the new increment is exactly p times the old increment.

With relative time \`t=n-(M+2)\`, old accumulated growth \`g_L(t-1)\`, set \`(κ,β)=(2,7)\` for t odd, \`(0,1)\` for t even. Then

    h = gcd(M+t+κ, |2t+β−g_L(t−1)|).

For a **COMMON predetermined T**, the first split is determined exclusively by old trace using \`q|2t+β−g_L(t−1)\` and \`M+t+κ≡0 mod q\`. Fixing \`M mod2L\`, the p possible lifts mod2Lp split in exactly the number of distinct compatible residues in this finite old-trace set. This is exact, not independent-trials probability.

For fresh prime \`p>12L+7\` and \`T≥6L+2p\`, the old wheel has settled before any possible p-hit, so exactly TWO of the p lifts split. This \`2/p\` does NOT hold automatically for dense p, prime-power q, or varying natural cutoff \`T_M=K(M)-(M+2)\`.

## 2. Exact sign barrier: cancellation is confined to q≤2L (paper)

At first split, old increment e0 and new increment p e0 differ by \`(p−1)e0\`, where \`p^v_p(L)|e0\`. The old trajectory's entire future growth after the split is at most \`2L−2\` by the next-even-multiple-of-L barrier; all future new growth is ≥0. Therefore:

    BOXED: ΔG=G_(Lp)(M)−G_L(M)
           ≥ (p−1)e0−(2L−2)
           ≥ (p−1)p^v_p(L)−(2L−2).

If \`q=p^(v_p(L)+1)>2L\`, then \`p−1≥2(L/p^v_p(L))\`, and **every split** has \`ΔG≥2\`; no split means ΔG=0. This holds for an arbitrary common finite cutoff, without assuming the two paths later agree, and needs no firing-count control.

For q>3, the exact successive q-firing congruences require ≥q−1 EVEN intervening horizon growth; between q-firings only L-divisor increments occur, with <2L total. Hence q>2L also forbids **second q-firings**. The genuinely difficult region for both cancellation and refiring is q≤2L.

In the far-prime complete-lift case, the two affected trajectories each have exactly one p-hit and their eventual post-hit L-tail has growth \`B_±∈[0,2L−2]\`. Thus their signed stabilized mean per p lifts equals

    BOXED: 2 + (B_+ + B_- − 2)/p
           in [2−2/p, 2+(4L−6)/p].

This refines \`2/p\` from a split FREQUENCY to a signed growth contribution. It is near2 for p≫L but **cannot be iterated over the entire prime-power ladder**, because after inserting p the wheel L changes, usually making subsequent q≪L.

## 3. Reproduced cancellation example and new dyadic sample

From independent original-operand gcd:
- M=507,L45: nonunit events \`(510,3),(517,5),(522,9),(530,5),(534,3)\`, growth20.
- M=507,L315: events \`(510,3),(513,7)\`, growth8.
So \`ΔG=-12\`. The new e7 at n513 eliminates FOUR later hits of the old trajectory.

The source audit's X256 dyadic prime-power ladder through all q≤4X was re-executed and reproduced. Extending the SAME exact prime-power ladder with original parity-gcd recomputation to X512:

    I_X odd M      #M   # inserted prime-powers   Σ positive Δ   |Σ negative Δ|   Σ actual G   Σ M /4
    [256,512)      128             188                 12658             372           12286      12288
    [512,1024)     256             329                 25622            6342           19280      49152

For X512 the final \`ΣG=19280\` was also independently checked by the UNTRUNCATED original parity-gcd recurrence at every index for all 256 odd starts.

**Important interpretation:** cancellation IS real and sometimes large, but the X256 edge-case is **not** evidence that negative Δ is mathematically necessary for the asymptotic proof: at X512 the **positive-only sum** 25622 already lies below the target 49152. Neither finite block is large enough for the published \`M≥2501\` growth=>GOOD implication.

Signed individual insertion means may also be large and negative, even before grouping:
- X512, q43 insertion: signed total +4002, per-start mean +15.6328125.
- X512, q31 insertion: signed total −1770, per-start mean −6.9140625.
- X256, q47 insertion: signed total +2798, per-start mean +21.859375.
Hence no automatic "each insertion costs exactly2" outside the far-prime separated regime. An O(1) per-insertion *uniform* bound is an unproved candidate and a numerical C=2 bound is false.

## 4. Concrete non-tautological theorem to target

Let \`I_X=\{odd M:X≤M<2X\}\`, and arrange all odd prime powers q≤4X increasingly, yielding \`L_0=1,L_1,...,L_J\` with \`L_j=L_(j−1)p_j\`. Define \`Δ_j(M)=G_(L_j)(M)−G_(L_(j−1))(M)\`, using M's ACTUAL cutoff. The full odd gcd is recovered exactly at \`L_J\`; therefore \`G(M)=Σ_j Δ_j(M)\` (\`G_(L0)=0\`).

There are only \`J(X)=O(X/\log X)\` such prime powers. A genuinely NEW, sufficient *signed insertion-cost theorem* would be the uniform upper bound

    BOXED: for every inserted q_j≤4X,
      Σ_(M∈I_X) Δ_j(M) ≤ H(X)|I_X|,
      with H(X)=o(log X).                              (A)

Then \`Σ_(M∈I_X) G(M)≤J(X)H(X)|I_X|=o(X²)\`, satisfying the earlier published dyadic sufficient mean bound \`ΣG≤(1/4)ΣM\` for all sufficiently large X and implying infinitely many twin primes. A constant H, if true, is more than enough; small finite positive spikes rule out an unqualified H=2.

(A) is a **strong conjectural intermediate** (possibly false). It must be proved even in the **dense/refiring regime q≤2L**, with M-dependent cutoffs, incomplete 2Lp periods, and signed cancellations preserved. A slightly weaker, more useful version allows summable per-step boundary errors \`E_j(X)\` with total \`Σ_j E_j(X)=o(X²)\`; the period-boundary errors CANNOT simply be discarded when 2Lp exceeds the dyadic interval length. For q>2L the one-split sign barrier and the exact distant-prime mean may handle a limited subfamily.

The strongest contribution of the user's proposal is that it furnishes a *specific coupling* between neighboring finite wheels and a possible signed amortization, rather than directly asserting that adaptive gcd residues behave independently. The mathematical gap is a true **average insertion-cost bound**; the exact first-split criterion and finite cancellations do not prove it.

**No Cap B or twin-prime infinitude established; no new Lean kernel checks.**
