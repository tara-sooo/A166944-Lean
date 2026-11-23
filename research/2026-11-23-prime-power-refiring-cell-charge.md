# A166944: higher prime-power refirings have a bounded cell charge

Date: 2026-11-23 JST. **Status:** two exact arithmetic lemmas kernel-check in Lean 4.33.1; the multi-event potential budget below has an elementary paper proof; a direct-gcd finite audit passed. This does **not** prove an unrestricted dyadic mean bound, Cap B, or twin-prime infinitude.

This note extends the squarefree prime-insertion work in the public tree (pinned current base `bd180e3de0fe6e12cc3c3ea25d65a985445344eb`) to repeated firings at one newly added prime-power level. The one-step charge rule and q=3 boundary correction continue an earlier local A166944 mission derivation; this public note makes the q>=5 statement kernel-checkable and does not claim independent discovery. It is deliberately separate from the squarefree first-split/renewal results, e.g. [the 2026-11-23 L1 transfer](2026-11-23-squarefree-early-prime-cost-L1-residue-packing.md) and [the first-hit regeneration note](2026-11-23-squarefree-prime-first-hit-regeneration-and-fibre-transfer.md). No literature-wide novelty claim is made.

Reproducible artifacts: [Lean arithmetic lemmas](prime_power_refire_charge.lean) and [finite direct-gcd audit](prime_power_refire_charge_audit.py).

## 1. Setup and exact one-event formula

Let the odd final wheel be `N = qW`, where `q = p^(v+1) >= 5` is the newly added prime-power level and `W` is coprime to `p`. Thus the old wheel has `p^v W` and `N/q=W`. A clipped trajectory has an even horizon `C`; a nonunit event with odd increment `e | N` updates

```
C' = C + e - 1,        e | C-1  or  e | C+1.
```
A `q`-event is one with `q | e`. Define the q-cell counter

```
Phi_q(C) = floor((C+2)/(2q)).
```

**Lemma (Lean-verified, `PrimePowerRefireCharge.q_hit_cell_jump`).** For odd `q>=5`, even `C>=2`, odd `e`, and `q | e` with `q | C-1` or `q | C+1`,

```
Phi_q(C+e-1) - Phi_q(C) = (e/q + 1)/2.
```

The Lean statement uses an addition form of the same identity (no natural-number subtraction). To see the two parity branches, write `e=q h`; `h` is odd. In the `C=+1 mod q` branch, write `C=2qa+q+1`; in the `C=-1 mod q` branch, write `C=2qa+q-1`. Since `q>=5`, both initial cell values are `a`; the updated cell is `a+(h+1)/2` in either case. The floor boundary is the reason for the threshold `q>=5`. In an actual trajectory, `e | C±1` together with `q | e` implies the lemma's `q | C±1` hypothesis by divisibility transitivity.

For `q=3`, the even-index branch `3 | C-1` has initial cell `a+1`, not `a`, so its jump is `(e/3+1)/2 - 1`. The odd-index branch `3 | C+1` keeps the uncorrected weight. This correction is in the paper argument and exercised by the script; it is not yet a separate Lean theorem in this file. Corrected q=3 charges are nonnegative but can be zero, so they do not bound the number of q=3 events.

## 2. The one-wheel repeated-event budget

Fix one trajectory on final wheel `N=qW`, starting at even horizon `C0>=2` at time `t0`. Write `C_t` for the horizon after step `t`, so `C_{t0}=C0` and the step at `t` takes `C_{t-1}` to `C_t=C_{t-1}+e_t-1`. Let `B` be the least multiple of `2N` with `C0<=B`. Every step has odd `e_t | N` and `e_t | C_{t-1}-1` or `e_t | C_{t-1}+1`. The [Lean-verified even-multiple barrier](prime_power_refire_charge.lean) says that, whenever `C_{t-1}<=B`,

```
C_{t-1} + (e_t-1) <= B.
```
Since `N | B`, the hypotheses of that barrier hold at every step. Induction therefore keeps the entire trajectory below `B`. Also `C_t` is nondecreasing, so `Phi_q` is nondecreasing. The even-barrier statement is a direct port of the previously kernel-checked local `WheelCheckpoint.even_barrier`; no novelty claim is made for that lemma. For any endpoints `t0<=u<=v`, count transitions `u < t <= v`: charge a q-event by `(e_t/q+1)/2` and every other event by zero. The local lemma identifies each q-event's charge with its cell increase; non-q transitions have nonnegative cell increase. Telescoping gives

```
Sum_{u<t<=v, q|e_t} (e_t/q+1)/2
    <= Phi_q(C_v)-Phi_q(C_u)
    <= Phi_q(B)-Phi_q(C0)
    <= N/q = W.
```
The endpoint convention `u<t<=v` is intentional: it counts the transition into state `C_v`, not an event already included in `C_u`. For the last inequality, `B-C0<2N=2qW`, while `B` is a multiple of `2N`; hence the two floor values differ by at most `W`.

This is a **per-q, per-fixed-wheel trajectory** weighted bound. For `q>=5` each charged event costs at least one, so there are at most `W` q-events on that trajectory. The multi-step induction and telescope are elementary paper reasoning; the source kernel-checks the one-step barrier and the per-event formula, not a single packaged theorem over arbitrary traces.

## 3. Do not sum these ledgers across levels

The per-q charge systems are not a disjoint partition of events: an increment `e=15`, for example, is divisible by both `q=3` and `q=5`. The separate `W` bounds therefore cannot be added as if each recurrence event were charged exactly once. Nor is a q-event charge the same object as a signed endpoint refinement when the wheel is enlarged; this note proves no monotonicity of terminal growth under insertion.

The result supplies a controlled accounting tool for repeated firings at one prime-power level. It does not control interactions between different levels, dense small-prime insertions, variable cutoffs, incomplete dyadic classes, or the global signed mean required by the twin-prime route.

## 4. Finite check and formal verification

The direct-gcd script tests 22 `(q,W)` pairs with

```
q in {3,5,7,9,25,27,49,125,343},   gcd(q,W)=1,
```
including first levels and several higher powers. For every odd start `7<=M<=201`, it scans the original parity-specific gcd over a full `2N` clock period at each frozen horizon, checks the per-event cell increment (including the q=3 correction), verifies the one-step barrier, and checks the accumulated corrected charge is at most `W`. These are synthetic clipped starts with `C0=2M-2` on fixed truncated wheels, not replays of actual canonical A166944 histories.

Observed: **2,156 trajectories; 782 q-events; aggregate corrected charge 438; maximum charge on any one trajectory 3.** Run with:

```
python3 research/prime_power_refire_charge_audit.py
```

This is finite regression evidence, not the proof of the unbounded budget.

Portable reproduction from the repository root, after the pinned dependencies are available:

```
lake env lean research/prime_power_refire_charge.lean
```

The sparse clone in this session did not materialize its own `.lake` tree. Instead, the file was checked with the local `p2m-check` shim against the shared pinned environment (Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`); the command exited 0. `#print axioms` for both `PrimePowerRefireCharge.even_barrier` and `PrimePowerRefireCharge.q_hit_cell_jump` reports only `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, new axiom, or target-theorem claim is used.

## 5. Remaining obstruction

The open task is still a unique, signed accounting across the ascending prime-power/prime ladder that controls the dyadic mean at the actual variable cutoff. This per-level potential does not provide that attribution or estimate. Consequently this note is a partial structural result only: it neither proves Cap B nor closes any A166944 or Prove2Me theorem.
