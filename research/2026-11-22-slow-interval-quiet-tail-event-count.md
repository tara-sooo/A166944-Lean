# Slow intervals, quiet tails, and a square-root event-count criterion

2026-11-22 JST. **Status:** research handoff / paper deductions from the uploaded `A166944-Lean.zip` snapshot. Existing underlying Lean theorems were inspected in that snapshot; **the new deductions in this note have not themselves been compiled or kernel-checked**. Neither Cap B nor the twin-prime conjecture is proved.

## Definitions and exact source basis

Let `d(n)=a(n)-a(n-1)` and `D(n)=a(n)-n` for the actual A166944 recurrence with its original initial condition. For an attained canonical record `M>5`, put

- `s0=M+2`, with `d(s0)=M` and `D(s0)=2M-2`;
- `K=floor((7M-1)/4)` and `T=K-s0`;
- `N_M=#{r : s0<r<=K, d(r)>1}`, the number of *actual* nonunit increments in this fixed index interval;
- `Slow(i,j)` means `2<=i<=j` and
  `9*(D(j)-D(i))+32+8*floor(sqrt(D(j)+1)) <= 4*(j-i)`.

The source snapshot supplied in the conversation includes:

- `mission_scan/twin_proof/cap_bound/AllIndices.lean`: `interval_decomposition`, `twins_of_slow_interval`, and the mod-30 potential `W` with values in `[0,32]` via `WeightCertificate.lean`.
- `mission_scan/twin_proof/cap_bound/CapSampleExact.lean`: `cap_of_one_slow_interval` (a slow interval with `M+2<=j<=K` implies the fixed-`M` Cap B condition).
- `mission_scan/twin_proof/cap_bound/SlowIntervalMission.lean`: `mission_of_slow_intervals` (slow intervals with unbounded `D(j)` imply infinitely many twin primes); the close-canonical-hit alternative is also available.
- `mission_scan/twin_proof/cap_bound/slow_backward.md`: the even-`Q` blocking lemma for paths with no slow intervals.
- `mission_scan/twin_proof/index_window/ConditionalIndexCheck.lean`: `a_le_three_mul`, giving `D(n)<=2*n`.
- Public project framework: [CanonicalRecord.lean](../A166944/CanonicalRecord.lean), [RecordBarrier.lean](../A166944/RecordBarrier.lean), [TargetDefs.lean](../A166944/TargetDefs.lean).

These mission-snapshot files were read from the uploaded ZIP; the GitHub project links above are background/canonical coordinates and should not be mistaken for copies of every mission-snapshot theorem.

## Paper deduction 1: a slow interval must end with a long unit tail

For `Slow(i,j)`, choose `s` from `AllIndices.interval_decomposition`: `i<=s<=j`, every increment on `(s,j]` equals 1, `D(s)=D(j)`, and

`4*(s-i)+W(i,D(i)) <= 9*(D(j)-D(i))+W(s,D(j))`.

Combining with `Slow(i,j)` and `0<=W<=32` gives

`4*(j-s) >= 32+8*floor(sqrt(D(j)+1))+W(i,D(i))-W(s,D(j)) >= 8*floor(sqrt(D(j)+1))`.

Hence **a necessary condition** is

`j-s >= 2*floor(sqrt(D(j)+1))`.

Conversely, whenever `s<=j` and every increment on `(s,j]` equals 1, `D(s)=D(j)`. Therefore

`j-s >= 8+2*floor(sqrt(D(j)+1))`

is **sufficient** for `Slow(s,j)`, simply by substituting zero growth into the definition. These necessary/sufficient unit-tail lengths differ by at most eight indices. The necessary implication is a paper consequence of the inspected Lean interval decomposition, not a new compiled Lean declaration.

## Paper deduction 2: an explicit event-count sufficient condition for Cap B

Define

`R=floor(sqrt(2*K+1))`, `L=8+2*R`, `q=floor(T/L)`.

Assume `M` is an attained canonical record and `s0<=K`. Then

> **If `N_M<q`, Cap B holds for `M`.**

Proof: partition the first `q*L` index steps of `(s0,K]` into `q` disjoint blocks of length `L`. Since fewer than `q` steps have `d>1`, at least one block `(i,j]` has all `d=1`. Thus `D(j)-D(i)=0`. The inspected `a_le_three_mul` gives `D(j)<=2*j<=2*K`, so `floor(sqrt(D(j)+1))<=R`; therefore `4*(j-i)=4L>=32+8*floor(sqrt(D(j)+1))` and `Slow(i,j)`. Also `s0<=j<=K` and `D(j)>=D(s0)=2*M-2>=4`. Apply `CapSampleExact.cap_of_one_slow_interval`. (For `q=0` the hypothesis `N_M<q` is impossible.)

At the certified numerical threshold `M=45,895,573`:

```text
K=80,317,252
T=34,421,677
R=12,674
L=25,356
q=1,357
```

Thus **`N_M<=1,356` is sufficient** for Cap B at this value of `M`. This is a sufficient test, not a proof of a universal event-count bound.

## Paper deduction 3: a weaker infinite-subsequence route to twin-prime infinitude

As `M` tends to infinity along genuine canonical records,

`q(M)/sqrt(M) -> 3/(4*sqrt(14)) = 0.2004459... `.

Suppose genuine attained canonical record values are unbounded, as proved in the project, and

`liminf_{M->infinity, M genuine canonical record} N_M/sqrt(M) < 3/(4*sqrt(14))`.

Then arbitrarily large such `M` have `N_M<q(M)`, hence a slow interval `[i,j]` with `j>=M+2` and `D(j)>=2M-2`. Consequently for every `N` there is a slow interval ending with `D(j)>N`. Applying the inspected `AllIndices.mission_of_slow_intervals` gives infinitely many twin primes.

In particular, **`N_M=o(sqrt(M))` along an unbounded subsequence of genuine canonical records** is sufficient. This is strictly weaker than proving Cap B at every record. The missing input is the actual asymptotic sparsity statement, not the conditional logical implication.

## Complementary diagnostic: nested even-Q blocking costs

The uploaded `slow_backward.md` gives: if there is no slow interval on `[s0,K]`, then for each even `Q>=2`, **each** full block of length

`L(Q)=ceil((9*(Q-2)+32+8*R)/4)`

contains an actual step `d(r)` not dividing `Q`. Define `E_Q` as the count of such steps. Hence `E_Q>=floor(T/L(Q))`.

For the divisibility chain

`2 | 6 | 30 | 210 | 630 | 6930 | 90090 | 1531530`,

the smallest possible odd nondivisor is respectively

`3,5,7,9,11,13,17,19`.

The event sets `{d: d does not divide Q}` are nested. Summing the incremental minimum contributions `(b_i-b_{i-1})E_{Q_i}` with `b_{-1}=1`, at `M=45,895,573` gives:

| Q | L(Q) | Required E_Q | Incremental lower bound on G |
| ---: | ---: | ---: | ---: |
| 2 | 25,356 | 1,357 | 2,714 |
| 6 | 25,365 | 1,357 | 2,714 |
| 30 | 25,419 | 1,354 | 2,708 |
| 210 | 25,824 | 1,332 | 2,664 |
| 630 | 26,769 | 1,285 | 2,570 |
| 6,930 | 40,944 | 840 | 1,680 |
| 90,090 | 228,054 | 150 | 600 |
| 1,531,530 | 3,471,294 | 9 | 18 |

Therefore, **no slow interval entails `G=D(K)-D(s0)>=15,668`** at that threshold. This number is an exact arithmetic consequence of the blocking estimate and the listed choices of `Q`, but it is far short of a contradiction with the possible first-breach growth budget. The moduli can be changed per block, and the interaction among different prime factors remains the unresolved issue.

## What remains open / next verification

1. **Main mathematics:** prove `liminf N_M/sqrt(M)<3/(4*sqrt(14))` over genuine unbounded canonical records, or any sufficient unbounded family of slow intervals. Local first-hit/CRT constraints and finite examples do not yet give that global count bound.
2. **Alternative:** prove uniform Cap B directly via the selective growth `H` and its known conditional reductions. Completing either route suffices; both are not required.
3. **Formalization:** add Lean declarations for the quiet-tail necessity, the block-count-to-slow condition, and the infinite-subsequence corollary, proving the needed count and convergence details. The original mission-snapshot files may need importing/porting to the repository’s pinned Lean environment.
4. **Computational status:** the formulas and the threshold arithmetic in this note have been rechecked separately; no new Lean build, large sweep, or platform submission has been performed.

No claim of having proved Cap B or the twin-prime conjecture is made by this note.
