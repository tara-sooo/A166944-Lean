# A working guide to Lean 4 tactics, as measured in this repository

Companion to `TACTICS.md` (which is the short cost/availability table). This is the explanation:
what each family of tactics is *for*, tested on goals shaped like A166944's.

Everything marked ✅ was run successfully on this device. Anything unmarked should be assumed
untested.

---

## 1. The four things a tactic can do

Every tactic in Lean falls into one of these jobs. Knowing which you need is most of the skill.

| job | tactics |
|---|---|
| **rewrite** the goal using a known equality | `rw`, `simp`, `ring_nf`, `field_simp`, `push Not` |
| **decide arithmetic** it can see | `omega`, `linarith`, `nlinarith`, `norm_num`, `ring`, `positivity` |
| **split** the goal into cases / parts | `constructor`, `rcases`, `obtain`, `by_cases`, `induction`, `cases` |
| **close** by computation or search | `decide`, `rfl`, `exact`, `assumption` |

When a proof stalls, the question is almost always *"which of the four am I missing?"* — not
"which tactic is stronger". A `nlinarith` failure on a `Finset` sum is a *rewrite* problem, not an
arithmetic one.

---

## 2. Arithmetic tactics, in increasing power and cost

### `rfl` / `decide` — computation ✅
`rfl` closes definitional equalities. `decide` closes any decidable proposition by evaluation:
```lean
example (n : Nat) : n + 0 = n := by rfl
example : Nat.Prime 5419 := by decide
```
`decide` is complete but can be slow; `Nat.Prime 2937930211` is impractical this way.

### `norm_num` — numeric evaluation ✅
```lean
example : (7:ℕ) % 3 = 1 := by norm_num
example : Nat.Prime 5419 := by norm_num        -- faster than decide
example : max 3 5 = 5 := by norm_num
```
**Trap:** on large numerals it overflows the recursion limit —
`error: (kernel) deep recursion detected`. Fix with `set_option maxRecDepth 100000` at file top.
With that, `Nat.Prime 2937930211` compiles in **93 s**, so large-prime checks belong in CI.

### `omega` — linear arithmetic over `ℕ`/`ℤ` ✅
Handles `+`, `-`, `<`, `≤`, `=`, `%` by a constant, and case splits. It is the workhorse:
```lean
example (n : Nat) (h : n ≥ 5) : n ≥ 3 := by omega
example (a b : ℕ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by omega
example (a b : ℕ) (h1 : a < b) (h2 : b < a) : False := by omega
```
**What it cannot do** (all tested):
- division by a variable, and `Nat.sqrt`, `Nat.minFac` (opaque functions);
- a modulus result feeding an existential: `n % 2 = 0 → ∃ k, n = 2*k` fails;
- bare divisibility: `q ∣ N → ¬ (q ∣ N+1)` fails until you extract `q ∣ (N+1) - N` first.

**Note on `Nat.dvd_sub` in this Mathlib:** it takes **two** arguments
(`Nat.dvd_sub h2 h : q ∣ (N+1) - N`), not the three used in some other versions.

### `linarith` / `nlinarith` — linear and nonlinear ✅
`linarith` proves linear consequences of hypotheses over ordered (semi)rings:
```lean
example (x : ℚ) (h : x > 0) : x + x > 0 := by linarith
```
`nlinarith` adds products, but **needs a hint** naming the nonlinear fact:
```lean
example (M : ℕ) (hM : 143 ≤ M) : 16 * (8*M + 4) < (M - 7) * (M - 7) := by
  nlinarith [sq_nonneg (M - 7 : ℤ)]      -- ✅ with the hint
                                           -- ✗ without it
```
The hint is the whole trick: `nlinarith` will not invent `sq_nonneg`.

### `ring` / `ring_nf` — ring normalisation ✅
```lean
example (a b : Nat) : (a+b)^2 = a^2 + 2*a*b + b^2 := by ring
example (a b : Nat) : (a+b)^2 = a^2 + 2*a*b + b^2 := by ring_nf   -- leaves normal form
```
`ring` closes; `ring_nf` rewrites the goal into normal form and lets you continue. For a `Nat`
goal with subtraction, `ring_nf` may leave `Nat` truncation obligations — follow with `omega`.

### `positivity` ✅
```lean
example (n : Nat) : 0 ≤ n := by positivity
```
Also fills side goals like `0 < 2` that other tactics leave behind.

### `gcongr` ✅
Proves `f a ≤ f b` from `a ≤ b` when `f` is monotone:
```lean
example (a b c : Nat) (h : a ≤ b) : a + c ≤ b + c := by gcongr
```
Very effective for `∑`/`*`/`^` goals where you want to apply a bound inside a context.

---

## 3. Structural tactics

### `constructor` — split `∧`, `↔` ✅
```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by constructor <;> assumption
```
For `↔`, `constructor` gives the two directions. **This matters for axioms**: closing an `iff`
with a bare `omega` pulls in `Classical.choice`; splitting with `constructor <;> intro h <;> omega`
does not (see `CLASSICAL_CHOICE_AUDIT.md`).

### `rcases` / `obtain` — decompose hypotheses ✅
```lean
example (p q : Prop) (h : p ∧ q) : p := by obtain ⟨hp, hq⟩ := h; exact hp
example (n : Nat) (h : ∃ k, n = 2 * k) : n % 2 = 0 := by obtain ⟨k, hk⟩ := h; omega
```
`rcases h with a | b` for disjunctions. Prefer these over `cases` when you want to name parts.

### `by_cases` — decide a proposition ✅
```lean
by_cases h : Nat.Prime n
```
**Caution:** it goes through `Decidable`, which for some shapes resolves to `Classical.dec`. When
that happens use `Nat.lt_or_ge` (constructive) instead.

### `induction` / `cases` ✅
```lean
example (n : Nat) : 0 ≤ n := by induction n with
  | zero => simp
  | succ k ih => omega
```

---

## 4. Rewriting tactics

### `rw` — directed rewriting ✅
```lean
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by rw [h]
```
`rw [← h]` rewrites right-to-left. **The single most common failure** is "did not find an
occurrence of the pattern" — usually because the term is not in the syntactic form you think.
Check with `#check` and prove the needed identity as its own `have` first.

### `simp` — oriented rewriting to normal form ✅
```lean
example (n : Nat) : n + 0 = n := by simp
example (l : List Nat) : l ++ [] = l := by simp
```
Over-eager `simp` can close the goal *and* remove what you needed next. `simp only [lemma]` is
the safe form.

### `push Not` — move negation inward ✅
Replaces the deprecated `push_neg`:
```lean
by_contra hlt
push Not at hlt      -- ¬ (a ≤ b)  becomes  b < a
```

### `field_simp` ✅
```lean
example (x : ℚ) (hx : x ≠ 0) : x / x = 1 := by field_simp
```

---

## 5. Logic

### `by_contra` ✅
```lean
example (p : Prop) (h : ¬¬p) : p := by by_contra h2; exact h h2
```
This was **absent** in the campaign's core-only phase and forced awkward `Nat.mod_two_eq_zero_or_one`
+ `exfalso` workarounds. It is available now.

### `calc` — chain of relations ✅
```lean
example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  calc a ≤ b := h1
    _ ≤ c := h2
```
Indispensable when a single tactic will not see the whole chain. The campaign used this to
replace leaking `omega` calls.

---

## 6. Casts between `ℕ` and `ℤ`/`ℚ` ✅
```lean
example (a b : ℕ) (h : (a:ℤ) ≤ b) : a ≤ b := by exact_mod_cast h
example (a b : ℕ) (h : a ≤ b) : (a:ℤ) ≤ b := by exact_mod_cast h
```
This is how you get `nlinarith` (which prefers `ℤ`) to work on `ℕ` goals: cast, then `nlinarith`.

---

## 7. A worked failure, and the lesson it produced

I tried to prove

```lean
example (n : Nat) : 2 * (∑ i ∈ Finset.range n, i) = n * (n - 1)
```

by induction, and burned several rounds on it. Every attempt failed:

1. `rw [Finset.sum_range_succ]` then `nlinarith` — the goal still contains
   `∑ x ∈ range k, (x + k)`, and **no arithmetic tactic looks inside a sum**;
2. `Finset.sum_add_distrib` — the rewrite pattern is `∑ x, (f x + g x)` but the goal is
   syntactically `∑ x ∈ range k, x + k`, so it does not fire;
3. `ring_nf` — normalises the sum term but leaves a nonlinear arithmetic obligation that still
   contains the sum.

The proof is **one line**, and it was already in Mathlib:

```lean
example (n : Nat) : 2 * (∑ i ∈ Finset.range n, i) = n * (n - 1) := by
  rw [Nat.mul_comm, Finset.sum_range_id_mul_two]
```

```
Finset.sum_range_id_mul_two : ∀ n, (∑ i ∈ range n, i) * 2 = n * (n - 1)
Finset.sum_range_id         : ∀ n, (∑ i ∈ range n, i) = n * (n - 1) / 2
```

**The lesson, which is the most important one in this file:** before writing any proof, search
Mathlib for the statement itself. `#check @Finset.sum_range_id` would have finished this in one
step. The campaign repeatedly confused "I cannot find a tactic that does this" with "this is hard";
nine times out of ten the answer was an existing lemma, and the skill is searching rather than
proving.

Practical search order, **all verified working on this device**:

1. `#check @<Module>.<guessed_name>` for a few plausible names;
2. **`exact?`** — searches the imported library for a lemma that closes the goal. Tested: on the
   *rearranged* goal `(∑ i ∈ range n, i) * 2 = n * (n - 1)` it answers
   `Try this: exact sum_range_id_mul_two n`. It does **not** find it on the original goal
   `2 * (...) = ...` because of the argument order — so rearrange first with `rw [Nat.mul_comm]`,
   then search;
3. **`simp?`** — reports exactly which lemmas `simp` used; tested on `n + 0 = n` it answers
   `Try this: simp only [add_zero]`, which is how you find the minimal `simp only` set;
4. `apply?` — for a goal where you expect a lemma with matching conclusion;
5. only then start proving by hand.

The key habit: **rearrange, then search.** `exact?` is syntactic-ish; a goal in a different but
equivalent form will not match.

## 8. Choosing a tactic — decision order

1. Is it definitional or decidable? → `rfl`, `decide`.
2. Are all terms numerals? → `norm_num`.
3. Is it linear (no variable products, no `sqrt`, no division by a variable)? → `omega` (for `ℕ`)
   or `linarith` (for ordered rings).
4. Are there products but a nonlinear fact you can name? → `nlinarith [that fact]`.
5. Is it an identity in a ring? → `ring` / `ring_nf`.
6. Is it monotonicity inside a context? → `gcongr`.
7. Does it need case analysis? → `rcases` / `by_cases` / `induction`.
8. Does it need a chain? → `calc`.
9. None of the above → the gap is a **lemma**, not a tactic. State and prove it separately.

Step 9 is the one the campaign kept forgetting: many "tactic limitations" were missing lemmas.
