# Cap B investigation: first breach, record gaps, and reproducible controls

Date: 2026-11-21 (JST).  Status: **partial research note, not a proof of Cap B or twin-prime infinitude**.

This note records a continuation of the A166944 investigation, distinguishing deductions from the established recurrence/Lean lemmas, independent finite computations, and unverified computational proposals. The Prove2Me [relaxed index cap (Cap B)](https://prove2.me/theorems/839fceee-b6d0-4f3c-96f2-510625db787a) and the overall conjecture remain **Open**.

## Definitions and existing verified inputs

Define `a(1)=2` and, for `n>=2`,

- even `n`: `a(n)=a(n-1)+gcd(n,a(n-1))`;
- odd `n`: `a(n)=a(n-1)+gcd(n-2,a(n-1))`.

Put `d(n)=a(n)-a(n-1)`, `D(n)=a(n)-n`.
For a genuine canonical difference record `M>5` at `n=M+2`, set

```text
s0 = M + 2,   H = D(s0) = 2M - 2,
K = floor((7M - 1)/4).
```

A moving-horizon state is `(s,C)` with `C=D(s)`, `s<C`. An event is the first index `r` in `(s,C]` with `d(r)>1`; writing `e=d(r)`, the next state is `(r,C+e-1)`. On a capped path the previously attained maximum `M` has not been exceeded. **Cap B** asserts `4*s_f <= 7*M - 1` for every such capped canonical path endpoint `s_f`, given the full hypotheses of the official theorem.

Existing source facts:

1. `A166944/CanonicalTravel.lean`: an event gap `g=r-s` obeys `g*g <= 4*(C+1)`.
2. `A166944/RebalancedCrossingGrowth210.lean`, private `moving_horizon_step_gap_potential6`: `2*g + P_after <= 5*(e-1) + P_before` with `P in {0,2}`; for canonical origin `P_start=0`, telescoping gives **`2*T <= 5*S`**, where `T=s-s0`, `S=C-H`.
3. `A166944/Lemmas.lean`: `D(s) <= 2*s`.
4. `A166944/RecordBarrier.lean`: `difference_records_unbounded`, and `capped_moving_horizon_eventual_exit` (a quiet return or a first new record).
5. The one-cap `Cap B -> A166944 target` route was reported as **SKETCH_ACCEPTED** on Prove2Me; that is a conditional reduction, not a full proof.

## 1. Paper reduction: certificate excluding a first crossing of Cap B

Fix a canonical record `M`; write `K=floor((7M-1)/4)`, `H=2M-2`, and `G=D(K)-H >= 0`.
Suppose an event on a capped replay **first** crosses the index bound: `s<=K<r`.
Since all increments between its predecessor `s` and event `r` equal 1,
`D(K)=D(s)=C` (also when `K=s`).

Let `Q=floor(sqrt(4*(D(K)+1)))`. Telescoping the mod-6 potential along the capped prefix to `s` (starting potential zero) gives

```text
2*(s-(M+2)) <= 5*G.
r-s <= Q.
```

Therefore, since `r>=K+1`, any first crossing necessarily satisfies

```text
  2*(K-M-1) <= 5*G + 2*floor(sqrt(4*(H+G+1))).   (FC)
```

**Contrapositive:** if the strict reverse inequality holds for an actual canonical record, no event can first cross `K`; this excludes a Cap B violating endpoint in its capped replay. The result is a paper-level composition of already-existing inequalities; it has **not** been packaged as a new Lean theorem.

At the certified record `M=45,895,573`:

```text
K                  = 80,317,252
H                  = 91,791,144
D(K)               = 91,793,058
G                  = 1,914
Q                  = 19,161
5*G + 2*Q          = 47,892
2*(K-M-1)          = 68,843,356
strict gap         = 68,795,464
```

Thus the sufficient inequality is overwhelmingly satisfied in this **one finite example**. Establishing an appropriate bound on `D(K)-H` uniformly for all canonical records is still open.

A separate elementary bound sums the event-gap square estimate together with `D(s)<=2s`: for `f(s)=sqrt(8s+4)`, each event makes `f` increase by less than 4. A first crossing by `p` events therefore requires

```text
p > (sqrt(8*(K+1)+4) - sqrt(8*(M+2)+4))/4.
```

At `M=45,895,573` this implies `p>=1,547`. This is a necessary condition, not a universal exclusion.

## 2. Conditional quantitative consequence: a Bertrand-type bound for twin primes

**Assume Cap B holds for every applicable canonical capped path and that the accepted one-cap reduction to the A166944 target is sound.** Fix a certified canonical strict record `M`. The existing exit dichotomy supplies the **next** strict record `R>M`:

- quiet exit: `R=C_f+1`;
- inside new-record event: `R=d(r)<=r<=C_f`.

Consequently `R<=C_f+1`. Independently, `D(s_f)=C_f<=2s_f`.
Cap B gives `4s_f<=7M-1`. Hence

```text
  2*R <= 2*C_f+2 <= 4*s_f+2 <= 7*M+1,
  R <= (7*M+1)/2.                                     (RG)
```

With the conditional A166944 target, every such record `R` is the larger member of a twin-prime pair.

Let `R_0=45,895,573` (the existing finite Lean certificate covers this record) and enumerate successive strict records `R_0<R_1<...`. Then

```text
  5*R_(j+1)+1 <= (7/2)*(5*R_j+1)
  5*R_j+1 <= (7/2)^j*(5*R_0+1).
```

For each real `x>=R_0`, a twin-prime pair with greater member in

```text
  (x, (7*x+1)/2]
```

would follow. Also, the number of twin-prime pairs with greater member at most `x` would be **at least**

```text
  1 + floor(log_(7/2)((5*x+1)/(5*R_0+1))).
```

The logarithmic expression is understood for `x>=R_0`; it counts the certified record-derived pairs only, so other twin-prime pairs can increase the total. These are **conditional consequences of Cap B**, not unconditional claims about twin-prime gaps. No Lean formalization of (RG) or the count is reported here.

## 3. Synthetic three-reset control: genuine local gcd dynamics, not a canonical record

Take an **artificial** state `M=27,541`, `s=M+2=27,543`, `C=2M-2=55,080`. Here both `M-2=27,539` and `M=27,541` are prime, but this state is **not** the actual A166944 state at that index (actual `D(27,543)=44,382`, `d(27,543)=1`).

Under the real gcd update rule, using the first nonunit gcd hit at each stage, we get

| predecessor `(s,C)` | event `r` | gap `g` | increment `e` | next `(r,C+e-1)` | next `X=2r-(C+e-1)` |
| --- | ---: | ---: | ---: | --- | ---: |
| (27543, 55080) | 27549 | 6 | 13 | (27549, 55092) | 6 |
| (27549, 55092) | 27567 | 18 | 37 | (27567, 55128) | 6 |
| (27567, 55128) | 27581 | 14 | 29 | (27581, 55156) | 6 |

This independently reproduced control shows three successive resets to `X=6`, including a decreasing increment (`37 -> 29`). It defeats any local argument asserting that such resets must strictly increase their increment or stop after two repetitions. It is **not** a counterexample to Cap B or to an authentic canonical replay.

## 4. Finite actual-trajectory probes

A standalone C++17 direct recurrence scan through `n=80,317,252`, starting at `a(2)=4`, gave:

- At `n=M+2=45,895,575`, `d(n)=45,895,573`, `D(n)=91,791,144`.
- At `K=80,317,252`, `D(K)=91,793,058`, hence `G=1,914`.
- Exactly **37** nonunit increments occur in `M+2<n<=K`; the last is at `n=45,896,532`.
- Across 16 certified canonical records `M>=968` with `K<=80,317,252`, the largest observed `G/M` was `102/2659 ~= 0.0383603`, at `M=2659`.

These are finite computational observations only. The accompanying programs were transient local checks and **are not claimed to be Lean-certified or part of this repository**.

Simple Python reproduction of the synthetic three-reset control:

```python
from math import gcd
M = 27541
s, C = M + 2, 2*M - 2
for _ in range(3):
    r = next(j for j in range(s+1, C+1)
             if (gcd(j, C-1) if j % 2 == 0 else gcd(j-2, C+1)) > 1)
    e = gcd(r, C-1) if r % 2 == 0 else gcd(r-2, C+1)
    assert e > 1
    print(s, C, r, r-s, e, C+e-1)
    s, C = r, C+e-1
```

## 5. Unresolved proof obligation and other exploratory claims

- The central obstruction remains **uniform control of `D(K)-(2M-2)`** (or an equivalent direct constraint on the authentic history/capped path); neither the first-crossing inequality nor the finite probes prove such control.
- Previous conversational experiments proposed stronger finite-state potentials `5T<=11S+22` and `6T<=13S+66` for canonical paths. **No reproducible complete graph/transition certificate or Lean source was committed with these claims.** Treat both as exploratory and independently re-audit before using them as formal lemmas or building further deductions.
- The synthetic reset constructions show why local gcd and nearby twin-primality information alone cannot establish the required global index bound; a proof may need authentic prefix/record-history restrictions.

**Canonical source of truth:** [A166944-Lean](https://github.com/tara-sooo/A166944-Lean), especially `ResearchDefs.lean`, `RecordBarrier.lean`, `CanonicalTravel.lean`, `RebalancedCrossingGrowth210.lean`, and `TwoCapGate.lean`. Official open Cap B: [Prove2Me](https://prove2.me/theorems/839fceee-b6d0-4f3c-96f2-510625db787a).
