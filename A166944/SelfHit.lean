import A166944.Lemmas

namespace A166944Research

/-!
# The self-hit identity: why Rowland's Lemma 1 does not transfer

Rowland's Lemma 1 (`arXiv:0710.3217`, §3) needs the **smallest prime divisor** `p` of
`(r-1)n₁ - 1` and concludes `n₂ = n₁ + (p-1)/(r-1)`, `g(n₂) = p`, `a(n₂) = r·n₁`.

A166944 has no such `r`: the recurrence branches on the **index parity** (`n % 2`), not on a
ratio `a(n)/n`.  On the fundamental subsequence (`B m = 2`, equivalently `a m = 2*m`) the
sieve collapses: the event value is *forced* by a self-referential gcd, so no smallest
prime divisor is ever computed.

The mechanism, on the odd index `n` reached just below the double:

* `a n = 2*n - 1`   (one step below the double)
* `d (n+1) = 1`     (so `a (n+1) = 2*n`, exactly the double)
* `d (n+2) = gcd (n+2-2, a (n+1)) = gcd (n, 2*n) = n`   (`n+2` is odd, so the odd branch applies)

Applied with `n = m+1` at a fundamental point `m` (`B m = 2`, so `d (m+1) = 1 ∧ B (m+1) = 1`,
hence `a (m+1) = 2*(m+1) - 1`), this yields `d (m+3) = m+1`: the next **record** `R = m+1`.

Contrast with Rowland's `r = 2` prediction: interpreting the fundamental point as `a = r·n`
would demand the gap `p - 1` with `p = spf(m-1)`; A166944 instead gives the constant gap `3`
and value `m+1` (`a(m+2) = 2(m+1)`, so `gcd(m+1, 2(m+1)) = m+1`).  The Rowland prediction is
therefore *not* transferable — no `minFac` machinery is required or usable here.
-/

/-- **Self-hit identity.**  If `n ≥ 2` is odd, `a n = 2*n - 1`, and `d (n+1) = 1`, then the
next event sits at the odd index `n+2` with `d (n+2) = n`.

The value `n` is obtained without any factorization: the odd branch reads
`d (n+2) = gcd (n+2-2, a (n+1))`, and the hypothesis `d (n+1) = 1` raises `a` to exactly the
double `a (n+1) = 2*n = 2*(n+2-2)`, so the gcd becomes `gcd (n, n*2) = n`. -/
theorem odd_self_hit {n : Nat} (hn : 2 ≤ n) (hnodd : n % 2 = 1)
    (ha : a n = 2 * n - 1) (hd : d (n + 1) = 1) :
    d (n + 2) = n := by
  have hsub : n + 2 - 2 = n := by omega
  have hsub1 : n + 2 - 1 = n + 1 := by omega
  -- `n + 2` is odd, so the recurrence takes the odd branch `gcd (n+2-2) (a (n+1))`.
  have hmap : d (n + 2) = Nat.gcd n (a (n + 1)) := by
    rw [d_eq_if_gcd_of_two_le (by omega : 2 ≤ n + 2),
      if_neg (by omega : ¬ (n + 2) % 2 = 0), hsub, hsub1]
  -- `d (n+1) = 1` together with `a n = 2*n - 1` pins `a (n+1)` to the double `2*n`.
  have han : a (n + 1) = 2 * n := by
    have hle : a n ≤ a (n + 1) := a_le_succ n
    have hd' : a (n + 1) - a n = 1 := by simpa [d, Nat.add_sub_cancel] using hd
    omega
  -- The self-hit: `gcd (n, 2*n) = n`.
  rw [hmap, han, Nat.gcd_eq_left ⟨2, (Nat.mul_comm n 2).symm⟩]

end A166944Research
