# High-growth canonical paths: exact terminal F envelope and an eight-index barrier

2026-11-22 JST. **Status:** paper consequence of previously Lean-kernel-checked first-hit and W-potential theorems, plus an exact finite recurrence audit. Cap B and twin-prime infinitude remain OPEN. No new Lean compilation.

Sources: the exact attached workspace `mission_scan/twin_proof/cap_bound/AllIndices.lean` (`twins_of_slow_interval`, `first_hit_bound`); `WeightCertificate.lean` (`W_le` giving `0<=W<=32`); `CapSampleExact.lean` (`cap_iff_twins_at_cutoff`); and public [A166944/Lemmas.lean](../A166944/Lemmas.lean). Previous research: [extremal-overdraw roughness](2026-11-22-extremal-overdraw-roughness-and-fixed-prime-reduction.md).

## 1. Precise setting and terminalization

For an **actually attained** canonical record M>=7, set

`s0=M+2, K=floor((7*M-1)/4), D(s0)=2*M-2, F(n)=4*n-9*D(n).`

We have `s0<=K<=2*M-2<=D(j)` for every `j in [s0,K]`.

**Terminalization theorem (paper deduction):** any slow interval `s0<=i<j<=K` can be extended to a slow interval `[i,K]`. The actual slow inequality is

`9*(D(j)-D(i))+32+8*isqrt(D(j)+1) <= 4*(j-i).`

Proof: the existing Lean `twins_of_slow_interval` shows `C-1,C+1` prime for `C=D(j)`. If a later nonunit event `r<=K<=C` existed, choose the first such event so its pre-horizon is `C`. At even `r`, the gcd `gcd(r,C-1)` is 1: the prime `C-1` is odd and its only positive multiple <=C is itself (odd). At odd `r`, `gcd(r-2,C+1)=1` since `r-2<C+1` and `C+1` is prime. Thus no later event exists, `D(K)=D(j)`, and extending to K increases `F` by `4*(K-j)` without changing the slow threshold.

Therefore

`(exists slow [i,j] contained in [s0,K]) iff (exists slow [i,K]).`   (1)

This is about slow witnesses, not an equivalence between slow and twin primality. `cap_iff_twins_at_cutoff` already proves an exact Cap B / terminal twin-pair equivalence under its hypotheses.

## 2. Exact event-boundary envelope even when total G is large

Let `s0=r0<r1<...<rN<=K` be the complete nonunit event indices, with gaps `g_h=r_h-r_(h-1)` and increments `e_h=d(r_h)>1`. Let `S=rN` if N>0, else S=s0; write `ell=K-S`. Define

`w_h=4*g_h-9*(e_h-1)=F(r_h)-F(r_(h-1)),`

`E_M=max_{0<=k<=N} sum_{h=k+1}^N w_h` (the empty suffix is zero),

`B_K=32+8*isqrt(D(K)+1).`

F increases by exactly four per index between nonunit hits. Its minimum in `[s0,K]` therefore occurs at `s0` or one of the event indices `r_h`. Telescoping gives

`F(K)-F(r_k)=4*ell+sum_{h=k+1}^N w_h.`

Combining with (1) gives the **exact iff**

`boxed: (some slow interval in [s0,K]) iff 4*ell+E_M>=B_K.`  (2)

No upper or lower hypothesis on the whole-window growth `G_M=D(K)-(2*M-2)` is required. The optimal comparison start is an event index, generally **not** s0.

## 3. The existing verified potential bounds E_M by 32

The already kernel-checked `AllIndices.first_hit_bound` gives, for every full event,

`4*g_h+W(r_(h-1),D(r_(h-1)))<=9*(e_h-1)+W(r_h,D(r_h)).`

Hence `w_h<=W(r_h,D(r_h))-W(r_(h-1),D(r_(h-1)))`. Summing over **any suffix** and using the verified `0<=W<=32` gives

`boxed: 0<=E_M<=W(S,D(S))<=32.`                               (3)

This holds for arbitrarily many events, arbitrary mixed prime/composite increments, and arbitrary phase changes. It is a consequence of an **already proven** potential inequality, not a new unrestricted growth estimate.

Let `t=isqrt(D(K)+1)`. Equations (2)-(3) give an **eight-integer-length boundary**:

- `ell<2*t`: no slow interval can occur in [s0,K].
- `ell>=2*t+8`: a slow interval necessarily occurs.
- `2*t<=ell<=2*t+7`: evaluate the exact `E_M` (or bound it by the terminal W) to decide.

Thus for the slow-interval approach, **high total growth cannot create an unbounded internal F recovery**; events can only contribute an additive at-most-32 correction to the final quiet tail.

## 4. Independent event-weight corollary

If the increment is a prime p>=11, the existing first-hit divisor bound `g<=2p` gives `w<=9-p<=-2`. If e>=9 is odd composite, choose a proper odd divisor f>=3 with e>=3f. Since `g<=2f`, `w<=8f-9(e-1)<0`. Only e=3,5,7 can give positive w, with respective maxima 6,4,2. Consequently

`0<=E_M<=min(32,6*N_3+4*N_5+2*N_7).`

If **all** events in the window have increment >=9, E_M=0 and (2) becomes an exact criterion:

`boxed: slow iff ell>=8+2*isqrt(D(K)+1).`                       (4)

This makes the high-growth obstruction concrete: an internal chain of large events cannot itself force a slow interval. The entire issue is how close the last event may remain to K.

## 5. Direct finite audit and a high-G example

[terminal_envelope_high_growth_audit.py](terminal_envelope_high_growth_audit.py) computes the **original** A166944 from a(1)=2 through n=2,500,000, including 250 nonunit events and 17 actually attained canonical records with cutoff K covered. At every index it independently scans the slow inequality against the running minimum of F, and confirms (1)-(4). **All 17** terminal-envelope equivalences pass: 14 records contain a slow interval, while M=7,13,43 do not.

Two **genuine** early high-growth/no-slow records:

`M=13: G=16, ell=2, E=0, B=80, 4*ell+E=8.`

`M=43: G=48, ell=9, E=0, B=120, 4*ell+E=36.`

An exact-gcd, but **artificial canonical-shaped** state illustrates the converse pattern. Set M=367, s0=369, D(s0)=732 and K=642, without claiming attainment from a(1)=2. The script computes every intervening parity-dependent gcd, finds 27 events and last event S=570, and checks all event increments <=M. The terminal horizon is D(K)=1020, and

`G=288, G/M=0.78474..., F(K)-F(s0)=-1500.`

Yet `ell=72, E=0, B=280` and `4*ell+E=288>=280`: a slow interval exists, first ending at j=640. The full-interval F falls substantially, but the terminal recovery produces a valid slow interval. A second artificial M=81 example has G=32, full F change -56 and terminal envelope 156>=136. These synthetic starts are NOT genuine canonical records.

## 6. Remaining genuinely global work

The high-G branch now has a **sharp terminal formulation**: along unbounded actually attained records, prove that the last nonunit event before K leaves a quiet suffix of length approximately `2*sqrt(D(K))` (within the eight-index boundary), or directly prove twin primality at D(K) using the previously checked exact Cap B theorem.

No local claim that many large growth events force an unbounded internal F drawup can work with the current fixed W potential: (3) already bounds the event-boundary recovery by 32. The missing number-theoretic input is a **global escape/termination estimate** ruling out paths that continue to generate nonunit hits within O(sqrt(M)) of K at arbitrarily large genuinely attained records.

Verification level: paper deductions from exact kernel-proved source, direct Python integer recurrence checks, preserved GitHub note and code. No new Lean compilation, no Cap B proof, and no twin-prime infinitude proof.
