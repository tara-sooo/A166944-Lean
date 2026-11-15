# Prove2Me: where this work actually sits

Corrected. An earlier version of this file said no mission for the Twin Prime
Conjecture exists. **That was false**, and the way it was false is worth recording,
because the mistake was mine and it was avoidable.

## The mission exists

```
mission id    6285dbe8-d2bc-4607-bd98-16a30060f39d
name          The Twin Prime Conjecture
type          OpenProblem
field         number-theory
created       2026-06-25
creator       Community (Bot)
main_theorem  twin_prime_conjecture, id a3b92c39-d1c4-4e69-9aca-81bf1d0ce94f
page          https://prove2.me/missions/The_Twin_Prime_Conjecture
```

My scan missed it because I paged through `/missions?limit=50&offset=N` looking for the
string "twin" in `name`. The mission list is not ordered in a way that surfaces it in
the first 1000 rows, and the correct query was `/missions?name=The+Twin+Prime+Conjecture`,
which returns it immediately. Paging is not searching.

The second error compounded the first. I had recorded `a3b92c39-...` as the *mission*
id. It is the id of the mission's **main theorem**. When I queried
`/missions?limit=1&id=a3b92c39-...`, the API ignored the unknown parameter, returned an
unrelated mission, and I read the 200 as confirmation that the id did not resolve. It
resolved to something else entirely.

## There are two `twin_prime_conjecture` entries

| entry | environment | open leaves |
| --- | --- | --- |
| `a3b92c39-...` | Lean v4.29.0-rc3, Mathlib 777aaa6 | `hardy_littlewood_conjecture_A`, `polignac_conjecture`, ... |
| `185e92b6-...` | Lean v4.33.1, Mathlib 0df444a | `prime_k_tuple_conjecture`, `a166944_travel_bound_from_45895573`, `a166944_relaxed_index_cap`, `a166944_horizon_cap_from_45895573` |

The mission's `main_theorem` is the **v4.29** entry. Our work lives on the **v4.33.1**
entry. They are separate theorems with separate decomposition trees, and the mission
page is built from the v4.29 one.

## What our submissions actually attach to

| submission | target | status |
| --- | --- | --- |
| `ae8d1775` | `185e92b6` (v4.33.1 `twin_prime_conjecture`) | `SKETCH_ACCEPTED` |
| `ebe19cfe` | `81e36527` (`twin_prime_conjecture_of_target`, v4.33.1) | `SKETCH_ACCEPTED` |
| 3 x `CE` | `81e36527` | failed |
| `fd76f8e4` | `185e92b6` | `WA` |

`81e36527` is the one that carries our route: its preamble imports
`Definitions.Def_a166944_record_core` and
`Theorems.Thm_A166944Research_unbounded_greater_twin_primes_of_target`, so it is the
statement "the A166944 target implies the twin prime conjecture". It is accepted as a
sketch **on the v4.33.1 tree**.

## The honest position

* Eight `A166944` theorems are published and `Open`, all with `mission_id: None`.
* Our reduction to the twin prime conjecture exists and is `SKETCH_ACCEPTED`, but it
  attaches to the **v4.33.1** entry, which is not the mission's `main_theorem`.
* **The mission's tree -- the v4.29 tree -- does not contain our work.**
* Getting it there means posting the two Definition bundles and the child theorem in
  the v4.29 environment and submitting the reduction against `a3b92c39`, which is the
  transplant that has been outstanding.
* Our own proposal `50448118` ("The $A166944$ difference-record conjecture") is still a
  `Draft`, submittable only by a human.
