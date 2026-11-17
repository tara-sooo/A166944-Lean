# What Mathlib tactics actually buy in this repository

Measured 2026-11-17, after Mathlib became locally available. Every claim here was run.

## The three-tier cost

| import | time | peak RSS |
|---|---|---|
| nothing (baseline) | 5.6 s | — |
| one narrow Mathlib module (`Data.Nat.Prime.Basic`) | 20–32 s | **1.9 GB** |
| `import Mathlib` (everything) | **132 s** | much more |

**Rule: import the narrowest modules that carry what you need.** `import Mathlib` is a 2-minute tax
per invocation and defeats the purpose. `import Mathlib.Tactic` is also expensive; prefer
`Mathlib.Tactic.Ring`, `Mathlib.Tactic.Linarith` individually.

## Tactics confirmed working (each tested on an A166944-shaped goal)

| tactic | example that works | notes |
|---|---|---|
| `ring` | `(a+b)^2 = a^2 + 2*a*b + b^2` | instant; replaces the hand-written `sq_expand` |
| `linarith` | `a ≤ b → a + c ≤ b + c` | linear only |
| `nlinarith` | `16*(8*M+4) < (M-7)^2` from `143 ≤ M` **with** a `sq_nonneg` hint | needs the hint; bare `nlinarith` failed |
| `positivity` | `0 ≤ n` | |
| `gcongr` | `a ≤ b → a + c ≤ b + c` | good for in-context monotonicity |
| `norm_num` | `Nat.Prime 5419`, `(2:ℕ)+2 = 4` | **see the recursion limit below** |
| `decide` | `Nat.Prime 5419` | works, but slower than `norm_num` |
| `omega` | `n < n + 1`; `¬ (q ∣ N+1)` from `q ∣ N`, `1 < q` **after** extracting the difference | **fails on bare divisibility, on `ℕ` division, and on `sqrt`** |
| `push Not` | replaces the deprecated `push_neg` | |

## The recursion trap in `norm_num`

`norm_num` on a large prime overflows the default recursion limit:

```
error: (kernel) deep recursion detected, use `set_option maxRecDepth <num>`
```

Fix: `set_option maxRecDepth 100000` at the top of the file. With it,
`example : Nat.Prime 2937930211 := by norm_num` compiles — in **93 s**, so large-prime checks are
expensive and belong in CI rather than in a tight edit loop.

## What `omega` still cannot do

Three shapes that failed in testing:

* `n % 2 = 0 → ∃ k, n = 2*k` (modulus into an existential);
* `Nat.sqrt n ≤ n` (opaque function);
* **bare `q ∣ N → ¬ (q ∣ N+1)`**: `omega` alone fails; it works once you extract
  `q ∣ (N+1) - N` with `Nat.dvd_sub` first, then `simp` the difference to `1`;
* any goal mixing `Nat.sqrt` or `Nat.minFac` with arithmetic.

Note `Nat.dvd_sub` in this Mathlib version takes TWO arguments (no inequality argument), unlike
its core-only usage. `Nat.dvd_sub h2 h : q ∣ (N+1) - N`.

For these use the Mathlib lemma directly (`Nat.lt_succ_sqrt`, `Nat.minFac_le_div`, …) and finish
with `linarith`, or state the needed fact as its own `have`.

## What this changes relative to the core-only campaign

The campaign spent many rounds working around absences that no longer exist:

| was avoided | now available |
|---|---|
| `Nat.Prime` absent, primality hand-rolled | `Nat.Prime`, `Nat.minFac_prime`, `Nat.exists_prime_and_dvd` |
| `ring` absent, squares expanded by `rw` chains (failed three times) | `ring` |
| `by_contra` absent | `by_contra` |
| `Nat.find` absent | `Nat.find` |
| `Nat.sqrt` hand-written as `isqrt` | `Nat.sqrt` + `Nat.lt_succ_sqrt`, `Nat.sqrt_le_sqrt`, `Nat.minFac_le_div` |
| `Classical.choice` had to be hunted down and removed | still worth auditing, but `linarith`/`omega` now bring it in legitimately |

`Nat.minFac` is the single most valuable addition: `Nat.minFac_le_div` gives
"composite ⟹ minFac² ≤ n" in four lines, which had been the missing step in Route A.
`RouteAMinFac.lean` is the first module using it.

## Axiom consequence, worth knowing before auditing

Mathlib tactics bring `Classical.choice` with them. `RouteAMinFac.lean`'s three declarations audit
to `[propext, Classical.choice, Quot.sound]`, whereas every core-only module in this repository is
`[propext, Quot.sound]` or axiom-free. This is not a defect — but a module's axiom report now
depends on whether it imports Mathlib tactics, so the audit in `CLASSICAL_CHOICE_AUDIT.md` must be
read with that in mind.
