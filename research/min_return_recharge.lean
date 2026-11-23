import Mathlib.Tactic

/-!
# Recharge between two and three selections of the same prime

The state is the even MIN horizon immediately before a selected prime `p`.
The signs of `C-1` and `C+1` are encoded as `C-1+2*a`, `a<=1`.
The gap `E` is the gain from OTHER selected labels between two p-hits,
excluding the update `p-1` at the first hit.
All theorems are elementary necessary conditions, not global return moments.
-/
set_option autoImplicit false
namespace MinReturnRecharge

private theorem no_even_multiple_below_two
    {p d : ℕ} (odd : p % 2 = 1) (even : d % 2 = 0)
    (pos : 0 < d) (short : d < 2*p) (dvd : p ∣ d) : False := by
  have ple : p ≤ d := Nat.le_of_dvd pos dvd
  have pd : p ∣ d-p := Nat.dvd_sub dvd (dvd_refl p)
  have zero : d-p = 0 := by
    by_contra hn
    have dp : 0 < d-p := Nat.pos_of_ne_zero hn
    have hle := Nat.le_of_dvd dp pd
    omega
  omega

private theorem even_multiple_below_four
    {p d : ℕ} (odd : p % 2 = 1) (even : d % 2 = 0)
    (pos : 0 < d) (short : d < 4*p) (dvd : p ∣ d) : d = 2*p := by
  by_cases h : d < 2*p
  · exact (no_even_multiple_below_two odd even pos h dvd).elim
  by_cases h2 : d=2*p
  · exact h2
  have hgt : 2*p < d := by omega
  have hpd : p ∣ d-(2*p) := Nat.dvd_sub dvd (by exact ⟨2, by omega⟩)
  have hpos : 0 < d-2*p := by omega
  have hlt : d-2*p < 2*p := by omega
  have heven : (d-2*p)%2 = 0 := by omega
  exact (no_even_multiple_below_two odd heven hpos hlt hpd).elim

/-- Each repeated p-hit must receive at least p-1 of other-label gain.
If that gain is no larger than 2p, it belongs to {p-1,p+1,p+3}. -/
theorem two_hit_recharge (p C E a b : ℕ)
    (hp : 5 ≤ p) (odd : p%2=1) (hC : 2 ≤ C)
    (evenE : E%2=0) (ha : a≤1) (hb : b≤1)
    (first : p ∣ C-1+2*a)
    (second : p ∣ C-1+(p-1)+E+2*b) :
    p-1 ≤ E ∧ (E≤2*p → E=p-1 ∨ E=p+1 ∨ E=p+3) := by
  let U := C-1+2*a
  let V := C-1+(p-1)+E+2*b
  have hu : p ∣ U := first
  have hv : p ∣ V := second
  have hUV : U < V := by dsimp [U,V]; omega
  have hdvd : p ∣ V-U := Nat.dvd_sub hv hu
  have hpos : 0<V-U := by omega
  have heven : (V-U)%2=0 := by dsimp [U,V]; omega
  constructor
  · by_contra hn
    have hshort : V-U<2*p := by dsimp [U,V]; omega
    exact no_even_multiple_below_two odd heven hpos hshort hdvd
  · intro hE
    have hshort : V-U<4*p := by dsimp [U,V]; omega
    have heq := even_multiple_below_four odd heven hpos hshort hdvd
    have hbalance : E+2*b=p+1+2*a := by dsimp [U,V] at heq; omega
    interval_cases a <;> interval_cases b <;> omega

/-- Two disjoint donor gaps between the first, second, third p-hits
must contribute at least twice p-1. -/
theorem three_hit_recharge (p C E₁ E₂ a b c : ℕ)
    (hp : 5 ≤ p) (odd : p%2=1) (hC : 2 ≤ C)
    (e1 : E₁%2=0) (e2 : E₂%2=0)
    (ha : a≤1) (hb : b≤1) (hc : c≤1)
    (first : p ∣ C-1+2*a)
    (second : p ∣ C-1+(p-1)+E₁+2*b)
    (third : p ∣ C-1+2*(p-1)+E₁+E₂+2*c) :
    2*(p-1) ≤ E₁+E₂ := by
  have h1 := (two_hit_recharge p C E₁ a b hp odd hC e1 ha hb first second).1
  have hC2 : 2 ≤ C+(p-1)+E₁ := by omega
  have h2a : p ∣ (C+(p-1)+E₁)-1+2*b := by
    convert second using 1 <;> omega
  have h2b : p ∣ (C+(p-1)+E₁)-1+(p-1)+E₂+2*c := by
    convert third using 1 <;> omega
  have h2 := (two_hit_recharge p (C+(p-1)+E₁) E₂ b c
    hp odd hC2 e2 hb hc h2a h2b).1
  omega

/-- No LOW-only gap with gain smaller than L can refire p>L. -/
theorem no_low_only_return (p C E a b L : ℕ)
    (hp : 5≤p) (odd : p%2=1) (hC : 2≤C)
    (evenE : E%2=0) (ha : a≤1) (hb : b≤1)
    (hE : E<L) (hL : L<p)
    (first : p ∣ C-1+2*a)
    (second : p ∣ C-1+(p-1)+E+2*b) : False := by
  have recharge := (two_hit_recharge p C E a b hp odd hC evenE ha hb first second).1
  omega

#print axioms two_hit_recharge
#print axioms three_hit_recharge
#print axioms no_low_only_return
end MinReturnRecharge
