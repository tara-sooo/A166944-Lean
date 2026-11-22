# A166944 squarefree wheel: reset-origin arithmetic dispersion, phase-free high-prime root widths, and deterministic renewal transport

Date: 2026-11-23 JST. Assigned [Issue #4](https://github.com/tara-sooo/A166944-Lean/issues/4), parent [Issue #1](https://github.com/tara-sooo/A166944-Lean/issues/1), branch `research/issue-4-terminal-survivor-positive-budget`. Continues [reset renewal and two-scale tails](2026-11-23-deficit-reset-renewal-and-two-scale-tail.md). **The algebraic identities below are PAPER proofs, NOT Lean kernel theorems. The tables are exact finite C++17 original parity-specific clipped squarefree GCD computations. Neither a uniform asymptotic reset-origin discrepancy estimate, a high-charged-run bound, twin-prime infinitude, nor the original A166944 strict-record conjecture has been proved.**

## 1. Exact reset-origin CRT root sets with SMALL, q-independent support

For even X>=256, set B=ceil(sqrt(7X)), P=3*5*7*11=1155 and L=2P=2310. At an actual event with a prime factor >=13, call it a *reset event* when its post-event deficit `z=2t-C` equals 0 for even t, or 6 for odd t. The full wheel uses original parity GCD `gcd(n,C−1)` at even n and `gcd(n−2,C+1)` at odd n, clipped by the squarefree odd-prime product <=B.

Let `E_{r,z}` denote the cumulative low-only growth values (INCLUDING zero) at all plateaus of the `{3,5,7,11}`-restricted continuation starting from `t mod L=r`, `C=2t−z`, `z in {0,6}`. This depends only on `(r,z)` and the finite original low-wheel transition graph. The earlier complete reset-manifold audit proves, computationally, `0<=e<=100`, all e even, at most 20 plateaus. At each such plateau,

    C_e(t)=2t-z+e.

For a new high prime q>=13, `q|C_e(t)−1` or `q|C_e(t)+1` holds iff

    t mod q in U_{q,r,z} := { inv2_q * (z−e+1), inv2_q * (z−e−1) mod q : e in E_{r,z} },

where `inv2_q` is the inverse of 2 mod q. Thus the ACTUAL reset origin t, rather than a product of earlier high primes, is the sole variable in the new q activation condition (as long as only low primes act before the next high event).

**New paper lemma with finite reset-manifold certificate (D1):** For every prime q>=103, the distinct numbers `e−1,e+1` for 0<=e<=100 differ in absolute value by at most 102<q, so reduction mod q creates no additional collisions. Hence

    |U_{q,r,z}| = u(r,z) := |{e−1,e+1:e in E_{r,z}}|,

independently of q>=103. Exhaustive enumeration of all 2*2310 reset residues gives **2<=u(r,z)<=31**, mean `sum_(r,z)u/(2L)=6.98398268` when the 4620 residues are uniformly weighted (NOT a statement about the actual origin distribution). These width bounds were rechecked by the new C++ source for every reset residue and q=103,107,127, whenever <=B.

**New paper refractory consequence (D2):** If q>=103 divides the increment of the preceding RESET event, then q is NOT in `U_{q,r,z}` for that very reset origin. For even reset the new C=2t is 0 mod q, and any low prefix yields C_e=e mod q, with e<=100 even: neither e±1 is zero mod q. For odd reset, `q|t−2` and C=2t−6 is -2 mod q; C_e=e−2 mod q, so neither `e−1` nor `e−3` is zero mod q. Thus the last-fired q>=103 cannot reappear in the next high event without an intervening OTHER high event. This is stronger than merely subtracting last-q candidates from the population: for these q the subtraction is IDENTICALLY ZERO. All finite scans assert this.

## 2. The exact averaged discrepancy identity (NOT equidistribution)

For each `(r,z)`, let `mu_{r,z}(t)` be the nonnegative INTEGER multiplicity of actual high-event RESET visits at absolute time t with `t mod L=r` and deficit z, across odd canonical starts M in [X,2X). The same state may be visited by many starting M. Let

    R_X = sum_(r,z,t) mu_{r,z}(t)           [total reset visits],
    A_q = sum_(r,z,t) mu_{r,z}(t)*1{t mod q in U_{q,r,z}},
    E_q = (1/q)*sum_(r,z,t) mu_{r,z}(t)*u(r,z),   for prime q>=103.

`A_q` counts candidate q ACTIVATIONS over all reset-low-only prefixes, **not** events that actually fired q. Prefixes after individual original cutoffs are intentionally included, so A_q is a deterministic upper count for appearances of q at the first subsequent high event after a reset.

There is an exact identity, with no mixing assumption:

    sum_(103<=q<=B prime) q*E_q
       = pi_[103,B] * sum_(r,z,t) mu_{r,z}(t)*u(r,z)
       <= 31*pi(B)*R_X.                                (D3)

Define weighted residue discrepancy

    D_X = sum_(103<=q<=B prime) q * |A_q−E_q|.

Then

    BOXED: sum_(103<=q<=B) q*A_q <= 31*pi(B)*R_X + D_X.  (D4)

The Fourier content of the unsolved estimate is explicit. For `f=1_{U_{q,r,z}}` and `e_q(x)=exp(2*pi*i*x/q)`, write `hat f(a)=sum_(v mod q) f(v)e_q(av)` and `hat mu(a)=sum_t mu_{r,z}(t)e_q(at)`. Fourier orthogonality gives exactly

    A_q−E_q = (1/q)*sum_(r,z)sum_(a=1)^(q−1) hat f(a)*hat mu(−a).   (D5)

Controlling the right side after summing over q is the **adaptive reset-origin dispersion problem**. It cannot be replaced by the claim that each actual t is uniform modulo q. Pointwise, a reset origin may have strongly selected residues; q-specific deviations can be substantial, even when the aggregate signed errors cancel.

**Conditional implication (paper, OPEN assumptions):** If `R_X=o(X log B)` and `D_X=O(pi(B)*R_X)`, then (D4) gives total weighted q>=103 activation after resets `o(XB)`. The finitely many q in [13,101] contribute at most a fixed constant times `R_X=o(XB)` to the weighted first-subsequent-high-event factor sum, so this entire one-wave weight is o(XB). A stronger empirical-looking possibility is `R_X=O(X loglog B)` and the same relative aggregate discrepancy. These conditions remain open. **This bounds the first next high event after a reset only; CHARGED excursions can contain many additional high events, so it does NOT prove twin primes.** In fact, the reset-count bound `R_X=o(X log B)` alone would already make the reset-event count o(XB); the dispersion bound supplies stronger *weighted* control, not a substitute for controlling charged runs.

## 3. A second structural reduction: the exact reset-to-reset transport map

For a FIXED cutoff prime bound B, a post-reset state is fully specified by `(t,z)` with z=0 or6, because C=2t−z. Thus the entire FUTURE local recurrence is deterministic as a function of `(t,z)`, with no earlier CRT history. Let `F_B(t,z)` denote the first subsequent high-prime RESET state, ignoring each individual source's terminal cutoff if that next reset exists. Every original trajectory uses the same next state when it starts at that `(t,z)` and its cutoff reaches that time. The graph of `F_B` is strictly forward in t and hence acyclic. Different source histories can MERGE into the same node.

With `I_X(v)` the number of starts whose FIRST reset is node v, and with the source-specific cutoff K(M), the actual occupied reset-state counts satisfy the exact transport identity

    mu_X(v) = I_X(v)
             + sum_(u:F_B(u)=v) sum_(visits from M at u) 1{K(M)>=time(v)}.   (D6)

This equation is a bookkeeping identity and is not a bound: **the source-dependent deadline remains attached to each visitor**. It nevertheless replaces the product of all previous high primes by a one-dimensional forward deterministic state graph plus multiplicity/deadline data. A spectral/mixing or renewal-survival estimate for this concrete transfer mechanism is the new possible proof ingredient.

## 4. Fully exhaustive original-GCD audit of the actual origins and phases

Source: `research/reset_origin_dispersion_audit.cpp`. It exhaustively scans every canonical odd M in each dyadic window, uses exact prime-clock event jumps, independently spot-checks with literal one-step parity GCD on M=7..119, verifies old full growth/event/reset regressions, checks candidate containment of every NEXT high-q hit after a reset, asserts last-q>=103 exclusion, calculates all 4620 stable root widths, and checks that multiple visits to the SAME reset `(t,z)` always give the SAME next RESET node when both survive their cutoffs. All audits PASS at four dyadic sizes and a fifth off-dyadic size X=500000. The last full-wheel original-GCD start window additionally exercises fractional B=ceil(sqrt(7X)) and changing q-band edges. It also independently verifies the integer formula `sum_q q*E_q = pi_[103,B]*sum_reset u`.

| X | B | reset visits R_X | distinct (t,z) | maximal multiplicity | candidate count (q!=last) | uniform phase expected (q!=last) | observed/expected |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 4,096 | 170 | 2,865 | 466 | 72 | 10,555 | 11,014.72 | 0.9583 |
| 16,384 | 339 | 14,422 | 1,912 | 122 | 66,032 | 68,913.76 | 0.9582 |
| 65,536 | 678 | 73,941 | 7,771 | 250 | 398,193 | 395,578.01 | 1.0066 |
| 262,144 | 1,355 | 360,413 | 31,510 | 526 | 2,149,485 | 2,154,733.00 | 0.9976 |
| 500,000 | 1,871 | 705,758 | 60,504 | 1,016 | 4,429,630 | 4,447,927.77 | 0.9959 |

The measured `q!=last` phase baseline excludes records last fired by q. For q>=103 this exclusion is unnecessary in the actual *candidate count* by D2, but leaves a small q-dependent change to the phase baseline; (D3) and the next table use ALL records for those high q, which is the clean Fourier formulation.

| X | measured Σ_(q>=103) q A_q | exact phase Σ q E_q | Σ_(q>=103)q|A_q−E_q| / Σq E_q |
|---:|---:|---:|---:|
| 4,096 | 228,878 | 239,655 | 0.1909 |
| 16,384 | 3,572,772 | 4,074,630 | 0.1766 |
| 65,536 | 45,822,207 | 46,220,500 | 0.1596 |
| 262,144 | 443,142,225 | 442,947,909 | 0.0990 |
| 500,000 | 1,181,918,852 | 1,188,954,260 | 0.1040 |

The third column is the exact integer `pi_[103,B]*sum_(reset visits)u`; a noninteger apparent value in intermediate floating-point arithmetic is only numerical rounding. **The 9.9% figure is a sum of ABSOLUTE q-wise discrepancies**, not just a cancellation of plus and minus errors. The signed aggregate at X262144 differs from phase by only 194,316 (0.044%) for q>=103, while the absolute q-error is 43,864,006.

At X262144, reset depth bins (number of preceding reset events for same original start plus one) had q!=last observed/expected ratios 1.0011 for depth1, 0.9997 for depth2, 0.9940 for depths3–4 and 0.9958 for depth>=5. In contrast, INDIVIDUAL q observed/expected ratios ranged 0.6675 (q941) to 1.5139 (q1163); no per-prime independence or uniform ratio claim follows. The distinct reset nodes are only 8.74% of total visits at X262144 and 8.57% at off-dyadic X500000. There are 262,789 observed reset-to-next-reset links but only 22,768 distinct reset nodes with a known next reset successor; **every duplicate's successor agreed exactly** in this finite audit. The largest reset multiplicity at one `(t,z)` was 526. This high collision energy makes crude independent-start or naive large-sieve arguments potentially too weak without exploiting the renewal transport.

## 5. What would turn this into a proof

The exact q-root sets eliminate the multiplicative history modulus at EACH reset and expose a tractable q-independent phase baseline for q>=103. To use this globally one still needs:

1. A quantitative **reset mass/renewal estimate**, such as `R_X=O(X(log B)^A)` (or preferably `O(XloglogB)`), derived from the deterministic transport F_B with source cutoff deadlines.
2. A **q-averaged adaptive dispersion inequality** of the form `D_X=O(pi(B)R_X)`, rather than a false uniform-phase assertion at every single reset.
3. A separate **charged-run tail**. The previous paper criterion showed that `R_total=O(X(log B)^A)` together with `#{M:L(M)>B^β}=o(X)` for any β<1 would already suffice for the twin-prime terminal growth reduction: on good sources `T(M) <= (R(M)+1)*(1+L(M))`, total good growth `O(X B^(1+β)(logB)^A)=o(X²)`, while bad source count is o(X) and each has G<=3X. The new dispersion controls the weighted q makeup of reset-born high events, but is not sufficient without item3.

The transport graph makes the missing ingredient precise: establish controlled occupancy and residue dispersion of reset nodes **after repeated mergers**, plus a charged-excursion bound. The finite matches, even for deep epochs, are encouraging but are not a substitute for those two asymptotic estimates.

No Lean build, no main branch change, no public novelty/solution claim. Keep Issue #4 OPEN and parent #1 as integration tracker.

### Reproduce

```bash
g++ -std=c++17 -O3 -Wall -Wextra -Werror research/reset_origin_dispersion_audit.cpp -o /tmp/reset_origin_dispersion_audit
/tmp/reset_origin_dispersion_audit 4096 16384 65536 262144 500000
```
