# Cap B: an all-composite / 3–5–7 prime-free travel potential (2026-11-21)

**Status:** verified finite arithmetic certificate + paper reduction, **not** a Lean kernel proof; **Cap B remains open**. The complete reusable Python 3 verification source is [`cap_b_prime_debt_210.py`](cap_b_prime_debt_210.py) (no packages or network required). Existing A166944 event lemmas are in [`CanonicalGrowth.lean`](../A166944/CanonicalGrowth.lean), [`FirstHitForm.lean`](../A166944/FirstHitForm.lean), and [`ResearchDefs.lean`](../A166944/ResearchDefs.lean).

## 1. Event model and construction

For an actual moving-horizon first event `(s,C) -> (r,C')` put `g=r-s`, `e=d(r)`, `C'=C+e-1`. The existing Lean results say:

- `e` is odd and `e>=3`;
- `g<=2f` for every divisor `f>1` of `e` (`moving_horizon_step_gap_le_twice_increment_factor`);
- `g*e<=2*(C+1)` (`moving_horizon_step_gap_mul_increment_le_twice_horizon`);
- for every `s<j<r`, the appropriate even/odd gcd at constant `D=C` is 1.

Set `N=210=2*3*5*7`. For residues `s in [0,209]`, even `c in [0,209]`, define the **clipped first hit** by examining `j=s+g` for `1<=g<=14`:

```text
e0 = gcd(j,c-1,210)       if j even
   = gcd(j-2,c+1,210)     if j odd.
```

Take the first `g` giving `e0>1`, if any. A factor 3, 5, or 7 would necessarily hit within 6, 10, or 14 indices respectively; if there is no clipped hit by 14, there is none. This defines a deterministic edge to `(j mod210, (c+e0-1) mod210)` with weight `g-(e0-1)`. In addition, whenever `gcd(x,210)=e0`, include the edges for `x in {9,25,27,33}` with the *same first-hit gap* but successor horizon `c+x-1` and weight `g-(x-1)`.

There are exactly **22,050 states** (`210*105`), **18,900 states with clipped hits**, and **58,232 edges**. Starting with `V=0`, perform synchronous relaxations

```text
V_new(u) = max(0, V_old(u), max_{u->v}(g-(e-1)+V_old(v))).
```

The supplied script checks that the 19th comparison stabilizes and directly checks **every edge inequality**:

```text
g + V(after) <= (e-1) + V(before).              (E)
0 <= V <= 29.
```

For a canonical start `s0=M+2,C0=2M-2` with `M mod6=1`, `V(s0,C0)<=27` across all 35 residue classes of `M mod210`. The maximum 27 is attained at `M mod210=139`.

### Why (E) covers all composite increments, not just the finite table

If the true increment `e` has `gcd(e,210)>1`, then any earlier clipped hit would also be a true nonunit gcd hit. Thus the *true* first hit is exactly the clipped first hit in its residue state, and its clipped value equals `gcd(e,210)`. Consequently all increments `e in {3,5,7,9,15,21,25,27,33,35,105}` are covered by the listed graph edges.

If `e` is composite, let `f` be its smallest prime divisor. The existing factor bound gives `g<=2f`.

- If `f=3`, either `e in {9,15,21,27,33}` or `e>=39`; in the latter case `e-1-g>=32>=29`.
- If `f=5`, either `e in {25,35}` or `e>=45`; in the latter case `e-1-g>=34>=29`.
- If `f>=7`, `e>=f*f`, hence `e-1-g>=f*f-1-2*f>=34>=29`.

In all the large cases, since `V(after)-V(before)<=29`, (E) follows automatically. The seven exceptional composites are covered by the graph. **Therefore (E) applies to every composite increment and to the primes 3,5,7 at every authentic first-hit event.**

The fact that the 210-residue graph overapproximates which states occur in the true A166944 history is harmless: (E) is checked on all admissible residue states. The arithmetic proof reducing unbounded composite increments to the finite exceptions is separate from the script; the script also tests its inequality through `e=10000` as a diagnostic. This is a **paper proof conditional on the finite checked certificate**, not an additional Lean declaration.

## 2. Reduced prime-only travel debt

For a true event with a **prime increment `p>=11`**, define

```text
b = max(0, g + V(after) - (p-1) - V(before)).
```

For all other events `b=0`, by (E). Summing over any canonical first-event path gives, with `T=sf-(M+2)`, `G=Cf-(2M-2)`,

```text
T + V(sf,Cf) <= G + V(M+2,2M-2) + sum(b),
T <= G + 27 + sum_{prime p>=11} b.                 (PB)
```

This is sharper in the three finite controls below than the earlier mod-3 reduction with unpaid prime increments starting at 5, and eliminates the particularly troublesome prime-5 steps entirely.

Furthermore `V(after)-V(before)<=29`, `g<=2p` and `gp<=2(C+1)`. For `U=C+1`, these give

```text
b <= sqrt(U)+30.                                     (BS)
```

Indeed `g-p<=sqrt(U)` follows by considering `p<=sqrt(U)` (use `g<=2p`) and `p>sqrt(U)` (use `g<=2U/p`). A positive debt `b>0` also requires `g>=p-29`, hence

```text
p*(p-29) <= 2*(C+1).                                (SP)
```

Thus only a finite range of primes of size `O(sqrt(C))` can produce a positive debt in a bounded-horizon prefix.

## 3. First Cap B crossing requires many positive prime debts

Set `K=floor((7M-1)/4)`, `H=2M-2`. Suppose `(s,C)->(r,C')` is the *first* capped event crossing `K`, i.e. `s<=K<r`. Since the intermediate increments equal 1, `C=D(K)`; write `G=C-H`, `U=C+1`. If `N_bad` is the number of prior prime-increment events `p>=11` with `b>0`, then (PB), (BS) and the existing single-event square-gap bound imply

```text
K - M - 1 <= G + 27 + N_bad*(sqrt(U)+30) + floor(sqrt(4*U)).   (FC210)
```

At the independently replayed certified threshold `M=45,895,573`:

```text
K = 80,317,252
H = 91,791,144
C = D(K) = 91,793,058
G = 1,914; U = 91,793,059
K - M - 1 = 34,421,678
floor(sqrt(4U)) = 19,161
```

If a first crossing were to occur with **these** `M,G,U`, (FC210) would require **at least 3,580 positive prime-debt events**. The actual canonical segment has **37 events total**, and only **4** positive-debt prime increments `p>=11`; its endpoint is a quiet exit, not a crossing. The number 3,580 is a necessary count under the displayed finite-state data, **not** a universal event count bound and not a proof of Cap B for arbitrary `M`.

### Direct recurrence controls

The script uses the *unclipped* gcd first-hit rule for fixed numbers of steps, not the residue graph, and separately checks all events and (E). Results:

| Canonical `M` | number of events | `T` | `G` | prime-`>=11` debt | `V_start` | `G+V_start+debt` |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 5,419 | 9 | 75 | 54 | 13 | 9 | 76 |
| 45,895,573 | 37 | 957 | 1,914 | 216 | 0 | 2,130 |
| 5,875,882,249 | 26 | 45,417 | 30,564 | 15,106 | 27 | 45,697 |

The authentic-record status of the starting `M` values comes from the existing A166944 verified record prefix; this script verifies only the subsequent fixed number of first-hit steps, not primality or the entire original sequence history.

## 4. Open part

The finite potential pays all composite and prime 3/5/7 events, **but does not uniformly bound the total debt from larger prime increments**. In particular the still-open statement needed to close Cap B is a bound on either the sum of positive prime debts (and `G`) along all actual canonical prefixes, or another invariant excluding first crossings. The original [Cap B statement](https://prove2.me/theorems/839fceee-b6d0-4f3c-96f2-510625db787a) remains Open, and this Python certificate is not a Lean proof or an official submission.

**Reproduce:** `python3 research/cap_b_prime_debt_210.py`. The script is itself committed and the remote contents were checked after commit.
