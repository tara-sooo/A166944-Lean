# Correction: the proposed weakening of cap (A) is WRONG

Campaign note, 2026-11-16. This retracts a claim I made and recorded earlier in this session.

## What I claimed

That cap (A) `C <= 3M + 4` could be weakened to `C <= 2M`, because `TwoCapGate.b_tight` uses
cap (A) only through an upper bound on `isqrt (C + 1)`, and because I computed
`C_f/(2M) = 1.0188` and read it as "close to 1, so the bound holds".

## Why it is wrong

The ratio being **above** 1 is precisely the negation of the inequality. `C_f/(2M) = 1.0188`
means `C_f > 2M`, not `C_f <= 2M`.

The identity already in the campaign makes this immediate:

```
C_f = 2*M - 2 + S
```

so

```
C_f <= 2*M   <=>   S <= 2
```

Measured `S` is 102 at `M = 2659`, 2388 at `M = 355723`, 28692 at `M = 22933441`. So
`C_f <= 2*M` holds only at `M = 661`, where `S = 0` — and at `M = 43` even the existing cap (A)
fails. **I should have substituted into the identity before computing any ratio.**

## The actual numbers

`C_f/M` across the records:

| M | S | S/M | C_f/M | `C_f <= 3M+4` | `C_f <= 2M` |
|---|---|---|---|---|---|
| 661 | 0 | 0.00000 | 1.99697 | true | **true** |
| 1321 | 18 | 0.01363 | 2.01211 | true | false |
| 2659 | 102 | 0.03836 | 2.03761 | true | false |
| 5419 | 54 | 0.00996 | 2.00960 | true | false |
| 22933441 | 28692 | 0.00125 | 2.00125 | true | false |
| 183616423 | 66 | 0.00000 | 2.00000 | true | false |

`C_f/M` is pinned just above 2 and decreasing toward 2; `C_f <= c*M` needs `c >= C_f/M`, so no
integer `c < 3` can work for all records. **Cap (A) admits no useful weakening** — the only
slack is `c` from 3 down to about 2.04, which is not worth the churn.

## The secondary error

I also derived a threshold `M >= 256c/(4c-7)^2` for the gate from a "worst case `C = c*M`".
That case is unrealisable: `C = 2M - 2 + S` with `S >= 0`, so `C` cannot be an arbitrary
multiple of `M`. The whole threshold analysis was vacuous.

## What was salvaged

Two `Nat` lemmas found while trying to prove the false statement are true and independent of it,
and are worth keeping if they compile clean (a subagent is confirming):

* `sq_expand (a b : Nat) : (a+b)*(a+b) = a*a + 2*(a*b) + b*b`
* `numeric_core (M : Nat) (hM : 143 <= M) : 16*(8*M+4) < (M-7)*(M-7)`
* `window_helper` — uses only `4s+1 <= 7M` and `2M <= C+2`, no false premise.

`b_tight_two_mul` — the statement built on the false premise — is abandoned. It is not merely
hard to prove; with the real bounds it is **false**, which is why my `omega` attempts kept
failing on seemingly contradictory hypothesis sets.

## Lessons

1. **When an identity is available, substitute into it before comparing ratios.** `C_f = 2M-2+S`
   turns `C_f <= 2M` into `S <= 2` instantly.
2. **A ratio above 1 is the negation of the bound, not evidence for it.** This is the second
   time this session I have mis-read a margin in the wrong direction.
3. **Before deriving a threshold from a "worst case", check that the worst case is consistent
   with the other constraints.** `C = c*M` is impossible here.
4. The subagent working from this premise was told to stop; the false statement must not be left
   anywhere it could be cited.
