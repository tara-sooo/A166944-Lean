# The audit map: what is already known to be impossible

Written 2026-11-16 at the end of a long campaign. **Read this before attempting anything.**

The repository contains six `Audit*.lean` modules (56 declarations) that systematically record
which routes to `Target` are independent and which are not. They were written before the campaign
described below, and **most of the campaign's "discoveries" were re-discoveries of their content**.
This document indexes them so the next reader does not repeat that.

## The six audit modules

| module | what it establishes |
|---|---|
| `AuditRoutes.lean` | The twelve routes are **NOT independent** — they share the same conclusion. Route 1 says the index cap and the travel bound are *the same inequality*. Route 9 says bounding `S` alone is *circular*. Route 4 is a coordinate change, not a constraint. Route 3's count bounds admit any `q`. Route 5 refutes a method rather than confirming a diagnosis. |
| `AuditCapBRadius.lean` | cap (B) does not imply the event-count criterion (`R1_cap_does_not_imply_event_count`); the gap is unbounded in the constant (`R1_gap_is_unbounded`); cap (B) is weaker than the travel bound (`R1_capB_is_weaker_than_travel`). |
| `AuditCountFailures.lean` | The event-count criterion fails at `M = 13` and `M = 43`; `139` is not the smallest start. |
| `AuditExcessExistential.lean` | **The excess criterion (`8(S+p) <= 3M-9`) HOLDS at 139, 313 and 2659 while the count criterion FAILS at all three.** This is the exact separation the campaign spent a round re-deriving. |
| `AuditSharp48Domain.lean` | The constant `48` is **sharp** in the tree's own bound: the witness `191` rejects `47` and forces `48`, and `191` is outside the canonical domain (`191 % 6 = 5`), so the sharpness does not threaten canonical starts. |
| `AuditAttainmentLower.lean` | The attainment hypothesis is free, and the index lower bound is free — so a theorem taking them is not vacuous. |

## What the campaign (2026-11-16, rounds 1-15) re-discovered

| campaign "finding" | already in |
|---|---|
| the twelve routes converge / all targets are the same quantity | `AuditRoutes.lean` (R6) |
| the event-count criterion fails at `M = 2659` | `AuditExcessExistential.R4_at_2659` |
| cap B is weaker than the travel bound | `AuditCapBRadius.R1_capB_is_weaker_than_travel` |
| cap B fails at 13 and 43, holds from 139 | `AuditCountFailures`, `SBoundLemma` |
| travel and the index cap are the same inequality | `AuditRoutes.R6_route1` |
| bounding `S` alone is circular | `AuditRoutes.R6_route9_is_circular` |

Roughly **half of the campaign's 15 rounds** produced results already present in these modules.
The lesson is not that the campaign was worthless — several genuinely new facts were established
(see below) — but that **the audit modules must be read first**.

## What the campaign added that is genuinely new

* `CarryFactor.lean` — the firing factor is carried into the next horizon, so a prime cannot fire
  two consecutive events. Not in the audit modules.
* `CoprimeEvents.lean` — **only the prime 3 can divide two consecutive event values.** Measured
  900/900 pairs, 18/18 exceptions match the predicted configuration. New.
* `Mod3Gap.lean`, `LpfGap.lean` — `gap <= 2q` for `q` dividing the branch term, via **first-hit
  minimality**. The minimality technique is new and reusable: it converts a LOWER structural fact
  into an UPPER bound on the event index.
* `Mod3Gap.lean` also shows `3 | C +- 1  =>  gap <= 6`, measured 362/362 with zero exceptions.
* `EventCountCounterexample.lean` — the failing record is `M = 2659`, and it is the ONLY failure
  above the threshold (though `AuditExcessExistential` has the same instance).
* `CapBThreshold.lean` — cap (B) is exactly `travel <= (3M-9)/4`, hence *looser* than the frontier;
  and the observed `4/7` constant is an artefact of `sf/M -> 1`.
* `FrontierIsForced.lean` — `Cf <= 3M+4  <=>  2*sf <= 3M+4  <=>  2*travel <= M`, with the boundary
  ATTAINED at `M = 139` (69 vs 70) and `M = 313` (156 vs 157). The constant is forced.
* `FrontierMargin.lean` — above `M = 139` the frontier has at least 4.63x of room.
* `LargeIncrementInactive.lean` — the large-increment excess lemma is VACUOUS on every record:
  it needs `e/sqrt(M) >= 9.8` but the largest observed is 2.12.
* `WindowControlsS.lean` — the window `C_f - s_f = S + (M-4) - travel` is the only quantity the
  tree controls, and a successful quiet return gives a LOWER bound on `S`, not an upper one.
* `S_IS_RECORD_SPACING.md` — `S = M' - 2M + 1` exactly, so `S` tracks the record spacing.

## The one thing that remains

An upper bound on `S` (equivalently on `p`, equivalently the frontier). Every route to it in the
tree is a restatement of it (`AuditRoutes`), the margin is large (`FrontierMargin`), the
mechanisms tried are inactive (`LargeIncrementInactive`) or false (`AuditCountFailures`), and the
stop condition forces a twin-prime centre at each horizon (`S_IS_RECORD_SPACING.md`).

## A process rule that came out of this

`HANDOFF.md` and the audit modules are the first files to read. Before claiming a finding, grep
both `theorem` and **`private theorem`** (one campaign result turned out to be a special case of a
`private` lemma it had not seen), and check the six `Audit*` modules for the same statement.
