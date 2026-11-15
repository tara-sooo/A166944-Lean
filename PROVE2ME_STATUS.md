# Prove2Me: what is actually connected, and what is not

Written after repeatedly reporting a connection that does not exist. The
misreporting came from conflating two different things on the platform:

* a **theorem** (`twin_prime_conjecture`, id `185e92b6-...`, environment
  Mathlib 0df444a / Lean v4.33.1, status `Open`), and
* a **mission**, the curated container that a theorem has to belong to in order to
  appear on a mission's page and to receive submissions against its decomposition tree.

## What is verified, checked against the live API on 2026-11-15

| claim | status |
| --- | --- |
| our eight `A166944` theorems are published | **yes** — `a166944_room_quantum` and seven siblings, status `Open` |
| they belong to a mission | **no** — `mission_id` is `None` for all of them |
| a reduction from our work to `twin_prime_conjecture` is accepted | **yes** — submission `ae8d1775-fdca-4ce7-85b4-0a3fd5f0789c`, `SKETCH_ACCEPTED` |
| `twin_prime_conjecture` is a mission | **no** — it is a theorem |
| a mission for the Twin Prime Conjecture exists | **no** — a scan of the first 1000 missions returns two name matches, "Twin-Ordered Matrices" and "Random 2-SAT", neither related |
| the mission id `a3b92c39-d1c4-4e69-9aca-81bf1d0ce94f` resolves | **no** — the API ignores the unknown id and returns an unrelated mission, which is how the error survived several rounds of checking |
| our independent mission proposal stands | `50448118-5e03-...`, "The $A166944$ difference-record conjecture", status **Draft** |

## The three environments

```
leanprover/lean4:v4.33.1    Mathlib 0df444a    <- our theorems and solutions live here
leanprover/lean4:v4.29.0-rc3 Mathlib 777aaa6
leanprover/lean4:v4.30.0    Mathlib c5ea003
```

## Why "connected to the mission" was wrong

The reduction `ae8d1775` is real and accepted, and it does show that a proof of our
`Target` yields the twin prime conjecture *as stated on the platform*. What it does
**not** do is place our work inside a mission: no mission exists to place it in, and our
theorems carry no mission id. A reader browsing missions will not find this work.

The way to fix that is the independent proposal `50448118`, which is a Draft and can
only be submitted by a human. Until then the honest description of the platform state
is: theorems published, one reduction accepted, no mission membership.

## What is verified elsewhere

* `tara-sooo/A166944-Lean`: 157 modules, 2217 declarations, `DECLARATIONS.json` guarded
  by CI, axiom audit clean.
* Provenance for every module is in `REACH.md`, `GATE_MAP.md` and
  `ANALYSIS_WHY_STUCK.md`; the latter records why the remaining barrier has not moved
  and which four angles were tried and closed.
