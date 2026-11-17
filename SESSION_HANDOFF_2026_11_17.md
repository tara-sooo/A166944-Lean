# Handoff: state of the A166944 / Prove2Me work as of 2026-11-17

Written for the next session. Everything below is verified; nothing is aspirational.

## What is green

`git log --oneline -6` on `main`, all pushed, CI green:

    2e1d0f4  RouteSeparation            cap B's p bound is 4 orders too weak for cap A
    43b4c7f  PBoundSufficiency          p-bound slack above the threshold (643x)
    b1af80c  CappedAttackAudit          Cap-B audit: terminal route closed, sqrt refuted
    c96a9e9  EventCountAboveThreshold   the M=2659 refutation is BELOW the threshold
    efd4919  PlatformLeafReductions     the platform leaf IS the tree's RelaxedIndexCapCappedForm
    34b0066  SumBoundBasic              list/Finset sum bounds found via `apply?`

204 modules / 2695 declarations. Every delivered module: 0 errors, 0 warnings, no `sorry`,
axioms recorded per declaration.

## The working surface is the platform, not the repo

Mission: `185e92b6-5906-49df-9d6f-4d95ee47a58d` (`The_Twin_Prime_Conjecture`).

    GET /theorems/185e92b6-5906-49df-9d6f-4d95ee47a58d/open-leaves

returns 4 leaves, **all with 0 accepted submissions**:

| leaf | statement | status |
|---|---|---|
| `10346ea1` | `prime_k_tuple_conjecture` | closability 1, genuinely open — ignore |
| `3e21b815` | travel bound `2*(sf-(M+2)) <= M` | EQUIVALENT to `e17694c4` |
| `9f6a4ebb` | `4*sf <= 7*M - 1` (cap B) | see below |
| `e17694c4` | `Cf <= 3*M + 4` (cap A) | see below |

`185e92b6` is a **theorem**, not a mission listing — `GET /missions` will NOT find it by name.
Reach it by theorem graph or by slug `prove2.me/missions/The_Twin_Prime_Conjecture`.
This cost real time; do not repeat it.

## The two leaves, reduced

**cap B (`9f6a4ebb`)** is, by `PlatformLeafReductions.platform_hB_of_relaxed_index_cap_capped_form`,
exactly the tree's `RelaxedIndexCapCappedForm` (AttainmentIsFree.lean:85) — a strictly smaller
statement (no `IsGreaterTwinPrime`, no attainment witness). Work THAT, not the platform form.

**cap A (`e17694c4`)** is `S <= M + 6`, and is discharged by
`CanonicalTravel.canonical_horizon_bound_of_event_count` the moment `48*p*p + 1 < M` holds.
`EventCountAboveThreshold` shows that criterion fails at exactly M = 13, 43, 139, 313, 2659 — all
FAR below the leaf's threshold `45895573` — and holds at every record above it with at least 643x
of room. So cap A's open content is exactly: **prove `p^2 <= c*M` above the threshold.**

## Closed routes — do not retry

1. **Terminal route for cap B.** The terminal identities (`B Cf = 2`, `Cf % 6 = 0`, `Cf ± 1` both
   prime, next record at `Cf + 3`) are consistent with every `sf`, so they bound nothing.
   Refuted in `CappedAttackAudit`.
2. **`d r <= sqrt(C ± 1)`.** FALSE. Witness `e = 25 | 275 = 25*11` with `25 > sqrt 275`, and it is
   real data (first event at M = 139). Refuted in `CappedAttackAudit.dvd_offset_does_not_give_sqrt`.
   Consequence: `S <= Σ sqrt(C_i+1)` is unavailable, so that route to `S` is closed at step one.
3. **cap B ⟹ cap A.** No. `RouteSeparation` + `ExcessGap`: cap B allows `p <= (M-3)/8`, linear,
   while cap A's criterion needs `p <= sqrt(M/48)`. Factor 16595 at `M = 367232911`.
4. **Abstract ledger ⟹ cap.** No. `capB_iff_window_lower_bound` needs `4S + (M-7) <= 4W`, the
   ledger gives the opposite bound on `W`, and the slack is `3M-9`, which diverges linearly.

## MISTAKE TO NOT REPEAT — I re-derived existing theorems THREE TIMES

Each of these was already in the tree, and I spent a round proving it again:

| I "found" | already existed at |
|---|---|
| `d r ∣ C±1` (odd/even branch) | `Lemmas.moving_horizon_event_divisibility_even/odd`, lines 6101, 6110 |
| `2*p <= S` | `ExcessLower.two_mul_count_le_excess` |
| cap B's p bound is far weaker than event-count's | `ExcessGap.excess_count_allowance_is_far_above_event_count`, line 182 |

`RouteSeparation` (2e1d0f4) is therefore largely a duplicate; its only new content is pinning the
exact `48p²+1` threshold (2765/2766 at 367232911, 977/978 at 45895573).

**Rule for the next session: before writing any lemma, `grep` the whole `A166944/` tree for its
conclusion, including `private theorem`, and read the `Excess*`, `Count*`, `Audit*`, `Lemmas.lean`
modules first.** The tree is 204 modules; assuming a fact is missing because it is not in the last
file read is how this happened three times.

## Environment facts (measured today)

- Mathlib IS available. Narrow imports 20–32 s at ~1.9 GB peak; `import Mathlib` is 132 s — never.
- `A166944.TravelTarget` (which defines `Target`) now typechecks locally in 19 s.
- `Nat.dvd_sub` takes TWO arguments in this Mathlib version.
- Mathlib tactics bring `Classical.choice`; pure-core modules stay `[propext, Quot.sound]` or
  axiom-free. State the set honestly per module.
- Tool-first order that actually paid off: `apply?` gave the sum-bound lemma where `exact?` found
  nothing on all four goals tried; `exact?` needs the goal already in matching form.
- Verification command and the one-lean-at-a-time rule: see `TACTICS.md` and `ENVIRONMENT_TRAPS.md`.

## What I would do next, in order

1. Attack `RelaxedIndexCapCappedForm` (not the platform form) by reading `AttainmentIsFree`,
   `BCoordinates`, `AbsorptionCriterion` end to end FIRST, then grepping for any lemma whose
   conclusion mentions `4 * sf` or `7 * M`.
2. For cap A, attempt `p^2 <= c*M` above the threshold via `moving_horizon_path_first_crossing`:
   the only place `p` enters that proof is `canonical_old_crossing_event_count`. A sharper version
   of that single counting lemma would discharge the leaf, and the measured slack is 38x, so it is
   not a tightness problem.
3. Keep the platform DAG as the task list. Submit to the leaves, not to files.
