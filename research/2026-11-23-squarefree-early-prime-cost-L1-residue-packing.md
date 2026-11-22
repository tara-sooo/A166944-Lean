# A166944 squarefree prime insertion: first-moment renewal, exact safe-residue packing, and late-phase obstruction

**2026-11-23 JST. Status: two elementary paper lemmas, real exact-gcd finite experiments. Twin-prime infinitude, squarefree dyadic mean cost, and Cap B remain OPEN; no Lean kernel compilation.**

Follows:
- [universal 7-step zero-deficit bridge and four-residue L2 renewal](2026-11-23-universal-seven-step-zero-deficit-bridge.md);
- [squarefree sqrt-wheel reduction to O(sqrt X) per-prime signed average](2026-11-22-squarefree-sqrt-wheel-mean-reduction.md);
- [growth-adaptive prime-insertion safety and first-hit clock](2026-11-22-growth-adaptive-wheel-splitting-and-tail-bootstrap.md).

Reproducibility: [squarefree_early_L1_residue_audit.cpp](squarefree_early_L1_residue_audit.cpp) checks L1 AP sums from the original parity-specific first-hit clock. [safe_first_split_residue_audit.py](safe_first_split_residue_audit.py) checks the exact residue enumerator over primes and the deterministic energy packing.

## 1. NEW EXACT first-moment transfer (strictly weaker than prior second-moment hypothesis)

Let X be even, B=ceil(sqrt(7X)), and p be a fresh odd prime with 11<=p<=B inserted into the squarefree wheel L of all earlier odd primes. Let I_X be odd M∈[X,2X), and S be ANY subset satisfying:
- old G_L(M)=h(M) and the growth-adaptive safety p>6h(M)+7;
- first p event occurs in the EARLY phase (deficit 6 for odd event or0 for even);
- after at most7-step 3/5 bridge (if even first hit), a canonical state v is attained by cutoff;
- NO SECOND p-event occurs up to original cutoff K(M).

The exact regeneration theorem yields a bridge b∈{0,4,8}, and

    v=(2M−2+h(M)+p+1+b)/2=M+(p+h(M)−1+b)/2,
    v mod p∈{0,1,3,5},
    (p−1)/2 <=v−M <(7p+35)/12<7p/12+3,
    Delta_p(M)=G_(Lp)(M)−G_L(M)
              =p−1+b+H_L(v;K(M)) <=p+7+G_L(v).

For a fixed target v, its bridge b is determined by residue v mod p (0,1,3,or5), so if k_v different M map to v, they have identical OLD frozen terminal horizon 2M−2+h(M). As M increases in steps>=2, h decreases by at least4. Since safety entails 0<=h<(p−7)/6,

    BOXED: k_v <1+(p−7)/24.                       (FIBRE)

Let
    U_p={odd v: X<=v<2X+7B/12+4,
              v mod p∈{0,1,3,5}},
    T1_p(X,L)=Σ_(v∈U_p) G_L(v).

Then WITHOUT ANY complete-CRT 2/p hypothesis, and without a growth second moment,

    BOXED: Σ_(M∈S) Delta_p(M)
            <=(p+7)|S| + (1+(p−7)/24)*T1_p(X,L). (L1-TRANSFER)

This is strictly less demanding than earlier Cauchy-L2 transfer at the theorem-hypothesis level: an upper estimate of an AP first moment is enough, even if the AP second moment is huge. The old second-moment hypothesis implies the first moment bound by Cauchy-Schwarz since |U_p|=O(X/p+B/p+1).

**Concrete sufficient AP-L1 hypothesis (OPEN):**
    BOXED: T1_p(X,L) <= A X B / p                         (L1)
for an absolute A, for all such p and old prefix L and arbitrarily large dyadic X.

Then (L1-TRANSFER) and trivial |S|<=X/2 give

    Σ_(M∈S) Delta_p(M)
      <= (p+7)X/2 + A XB/p*(p+17)/24
      =O_A(XB).

Thus this weaker first-moment statement alone controls the ENTIRE EARLY SAFE ONE-SHOT portion of each prime stage at the scale required by the squarefree sqrt-wheel average-to-twin infinitude reduction. **It does not bound late, unsafe or repeated-p contributions**, so (L1) alone is NOT a twin-prime proof.

## 2. NEW short-interval deterministic candidate residue count (no probability/equidistribution)

For EVERY safe start M (not necessarily early or one-shot), h(M)=G_L(M) is EVEN and

    6h(M)+7<p   ==>   h(M)=2j,  0<=j<=J_p,
    J_p=floor((p−8)/12).

At the old terminal horizon C=2M−2+2j, p can be newly active only if

    p|C−1 <=> p|2M−3+2j,
    p|C+1 <=> p|2M−3+2(j+1).

Hence p|C±1 forces

    BOXED: 2M−3+2k==0 (mod p) for some 0<=k<=J_p+1.  (RESIDUES)

Since the odd starts M in any p consecutive positions run through each residue mod p exactly once, at most J_p+2 residue classes can cause a safe initial p-split. Thus an interval of N consecutive odd starts contains AT MOST

    BOXED: N_safe_split <= (J_p+2)*ceil(N/p)         (COUNT)

safe first-p splits, independently of the adaptive history. For p->infinity, the eligible residue proportion is at most ~1/12, rather than a constant-one fraction. The true experimental rate is usually much smaller; (COUNT) is a worst-case bound and does NOT establish the complete-lift exact 2/p rate in a short interval.

**Energy refinement:** Within each full p-block of consecutive odd starts, number b of safe split starts forces at least (b−2)(b−1) units of old growth among them. To see this, the k residue in (RESIDUES) has minimum compatible h at least 2max(k−1,0); the b cheapest distinct residues cost 0,0,2,4,...,2(b−2). Consequently

    BOXED: Σ_(M safe split in block) h(M) >= (b−2)_+(b−1)_+,

and for R consecutive full/partial p-blocks, W_safe=sum of old h among safe split starts,

    BOXED: N_safe_split <=2R+sqrt(R*W_safe).        (PACKING)

Both (COUNT) and (PACKING) are deterministic; neither assumes independence of the original first-hit process. This separates the direct p-hit cost from the downstream L-wheel renewal tail:
    Σ_(safe split) (p−1) <= (p−1)*(J_p+2)*ceil(N/p)
                         =O(N p/12 + p²) for p<=B,
which is already within the required per-prime O(XB) scale when N~X and p=O(sqrt X).

## 3. Finite L1 AP sums, exact squarefree prefix dynamics

Using only the original parity-dependent gcd rule, cap by the squarefree prefix of primes <p; sum G_L(v) on four residues v modp∈{0,1,3,5} in [X,2X+7B/12+4). For each dyadic X, check EVERY prime 11<=p<=B; define

    R1(X)=max_p [p*T1_p(X,L)/(X B)].

Observed:

    X          B    prime stages >=11    max R1(X)       maximizing p     T1 at maximizing p    #target v
    4096      170          35             2.852381089        149                 13330             56
    16384     339          64             2.759075694        269                 56968            124
    65536     678         119             2.071728687        619                148714            215

The observed first-moment normalized maxima are much smaller than the earlier second-moment maxima (9.17,14.89,5.94), though these are different quantities and cannot be compared as bounds without specifying norm conventions. These finite values make the AP L1 target a useful concrete experiment, NOT a proof of a uniform A.

Note on cutoffs: G_L(v) uses the natural cutoff K(v), while the one-shot transferred tail ends at the original shorter K(M), so H_L(v;K(M))<=G_L(v). The L1 audit computes the conservative longer growth.

## 4. Important late-phase counterexample to bounded regeneration

There is NO universal analog of the seven-step X=0 bridge for safe LATE p-hits. For example, take old wheel L=1, p=11, artificial odd M=39. Old growth h=0, safe threshold 11>7, old C=76, p|(C+1)=77. The first p hit is at odd index n=57, within K(39)=68, and gives

    X(57)=2p+6=28.

Since the enlarged wheel contains only p and the post-hit p-clock is inactive, ALL subsequent increments through cutoff are1, so X strictly increases by2 each step and NEVER returns to6. A blanket bounded-time late canonical renewal theorem would be FALSE. A late branch must instead be treated as a separate high-deficit L-tail / one-shot or p-refire component.

This example distinguishes an exact early-regeneration theorem from a conjectural global "all p hits regenerate" statement.

## 5. Remaining actual theorem needed

The main unproved short-interval input for EARLY SAFE ONE-SHOT sources is (L1), a first moment over four AP classes. To prove the FULL signed squarefree prime-stage mean bound E Δ_p<=C sqrt X (which already suffices for twin infinitude via an earlier conditional reduction), ALSO need:
1. late-phase first p hits with post X=2p or2p+6 (no forced bounded regeneration),
2. unsafe h≥(p−7)/6 and possible multiple p-hits,
3. potentially large post-hit L-tail costs and boundary effects.

A natural next tactic is a **joint dyadic AP first-moment inequality with a high-deficit tail budget**. Neither component is currently established. All new theorems in this note are elementary paper lemmas plus finite verifications, not Lean-certified universal theorems.
