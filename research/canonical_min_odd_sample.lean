import research.canonical_min_prefix
import Mathlib.Tactic

/-!
Two-step (positions 1,3,5,...) sampled prefixes of actual canonical MIN histories.
The original three-step certificates are left untouched. A non-twin completed
history is forced to make 4*P high selections; this yields 2*P sampled labels
among at most P available prime labels.

All global prime-correlation / return-moment estimates are still hypotheses.
-/
set_option autoImplicit false
namespace CanonicalMinPrefix

/-- First, third, fifth, ... labels. -/
def everyOther : List ℕ → List ℕ
  | [] => []
  | [p] => [p]
  | p :: _ :: tail => p :: everyOther tail

theorem everyOther_length : ∀ w : List ℕ,
    (everyOther w).length = (w.length + 1) / 2
  | [] => by simp [everyOther]
  | [p] => by simp [everyOther]
  | p :: q :: tail => by
    simp only [everyOther, List.length_cons, everyOther_length tail]
    omega

theorem everyOther_mem : ∀ (w : List ℕ) (p : ℕ),
    p ∈ everyOther w → p ∈ w
  | [], _, h => by simpa [everyOther] using h
  | [a], p, h => by simpa [everyOther] using h
  | a :: b :: tail, p, h => by
    simp only [everyOther, List.mem_cons] at h ⊢
    rcases h with eq | hit
    · exact Or.inl eq
    · exact Or.inr (Or.inr (everyOther_mem tail p hit))

/-- Take at most 2*P labels after retaining positions 1,3,5,... -/
def sampleOdd (P : ℕ) (w : List ℕ) : List ℕ :=
  (everyOther w).take (2*P)

theorem sampleOdd_mem {P p : ℕ} {w : List ℕ}
    (h : p ∈ sampleOdd P w) : p ∈ w :=
  everyOther_mem w p (List.mem_of_mem_take h)

/-- A length-4P high history yields at least P repeated sampled labels. -/
theorem sampleOdd_lower {P : ℕ} {S : Finset ℕ} {w : List ℕ}
    (card : S.card=P) (allowed : ∀ p ∈ w, p ∈ S)
    (long : 4*P ≤ w.length) :
    P ≤ repeats (sampleOdd P w) := by
  have hs : (sampleOdd P w).toFinset ⊆ S := by
    intro p hp
    exact allowed p (sampleOdd_mem (List.mem_toFinset.mp hp))
  have hle := Finset.card_le_card hs
  have hsize : 2*P ≤ (everyOther w).length := by
    rw [everyOther_length]
    omega
  have hlen : (sampleOdd P w).length=2*P := by
    simp [sampleOdd, List.length_take, Nat.min_eq_left hsize]
  unfold repeats
  omega

noncomputable def oddSampleAt (B y M : ℕ) : List ℕ :=
  sampleOdd (highSet B y).card (highWord y (canonical B M).1)

noncomputable def oddRepeatsAt (B y M : ℕ) : ℕ :=
  repeats (oddSampleAt B y M)

/-- A non-twin end needs >=4P actual high events, a stricter result
than the length guarantee used by the old 6P/thirds certificate. -/
theorem nontwin_odd_lower {B y L M : ℕ} (hM : 5≤M)
    (cut : ∀ p ∈ pool B, p≤y → p ∣ L) (pos : 0<L) (evenL : L%2=0)
    (square : 2*finish M+1<B*B)
    (travel : 4*(highSet B y).card*(2*B+3*L) < finish M-start M)
    (bad : ¬Twin (canonical B M).2) :
    (highSet B y).card ≤ oddRepeatsAt B y M := by
  have run := canonical_spec B M
  have bud := clock_budget run cut pos evenL square bad
    (by simp [start]) (by unfold start finish; omega) (by unfold initial; omega)
    (by unfold initial; omega) (by unfold start initial; omega)
  have long : 4*(highSet B y).card ≤
      (highWord y (canonical B M).1).length := by
    by_contra! h
    have hm := Nat.mul_le_mul_right (2*B+3*L) (by omega :
      (highWord y (canonical B M).1).length+1 ≤ 4*(highSet B y).card)
    omega
  apply sampleOdd_lower (S:=highSet B y) rfl _ long
  intro p hp
  have hh := List.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨run_mem run p hh.1, by simpa using hh.2⟩

theorem twin_of_odd_deficit {B y L : ℕ} (src : Finset ℕ)
    (cut : ∀ p ∈ pool B, p≤y → p ∣ L) (pos : 0<L) (evenL : L%2=0)
    (bounds : ∀ M ∈ src, 5≤M ∧ 2*finish M+1<B*B ∧
      4*(highSet B y).card*(2*B+3*L)<finish M-start M)
    (deficit : (∑ M ∈ src, oddRepeatsAt B y M) < src.card*(highSet B y).card) :
    ∃ M ∈ src, Twin (canonical B M).2 := by
  classical
  by_contra! bad
  have lower := Finset.sum_le_sum (s:=src) (fun M hM =>
    nontwin_odd_lower (bounds M hM).1 cut pos evenL (bounds M hM).2.1
      (bounds M hM).2.2 (bad M hM))
  have hlow : src.card*(highSet B y).card ≤ ∑ M ∈ src, oddRepeatsAt B y M := by
    simpa using lower
  exact (not_lt_of_ge hlow) deficit

theorem odd_window_certificate {u B y : ℕ} (u1 : 0<u)
    (square : 7*(4*u)≤B*B)
    (travel : 4*(highSet B y).card*(2*B+3*lowModulus B y)<3*u-2)
    (deficit : (∑ M ∈ sources u, oddRepeatsAt B y M) <
      2*u*(highSet B y).card) :
    ∃ p, 2*(4*u)-3≤p ∧ p.Prime ∧ (p+2).Prime := by
  have bounds : ∀ M ∈ sources u, 5≤M ∧ 2*finish M+1<B*B ∧
      4*(highSet B y).card*(2*B+3*lowModulus B y)<finish M-start M := by
    intro M hM
    obtain ⟨lo,hi,odd⟩ := mem_sources.mp hM
    unfold finish start
    omega
  obtain ⟨M,hM,tw⟩ := twin_of_odd_deficit (sources u)
    (fun p hp hy => lowModulus_cover hp hy) (lowModulus_pos B y)
    (by simp [lowModulus]) bounds (by simpa [sources] using deficit)
  have hs := (mem_sources.mp hM).1
  have mono := (canonical_spec B M).horizon_mono
  unfold initial at mono
  refine ⟨(canonical B M).2-1, by omega, tw.1, ?_⟩
  have e : (canonical B M).2-1+2=(canonical B M).2+1 := by omega
  rw [e]
  exact tw.2

/-- An unbounded supply of strict, actual odd-sample certificates forces
unbounded twin primes. The window-deficit input is NOT supplied here. -/
theorem unbounded_twins_of_odd_certificates
    (windows : ∀ N : ℕ, ∃ u B y : ℕ, N<u ∧ 7*(4*u)≤B*B ∧
      4*(highSet B y).card*(2*B+3*lowModulus B y)<3*u-2 ∧
      (∑ M ∈ sources u, oddRepeatsAt B y M)<2*u*(highSet B y).card) :
    ∀ N : ℕ, ∃ p, N<p ∧ p.Prime ∧ (p+2).Prime := by
  intro N
  obtain ⟨u,B,y,hu,hs,ht,hd⟩ := windows N
  obtain ⟨p,hp,h1,h2⟩ := odd_window_certificate (u:=u) (by omega) hs ht hd
  exact ⟨p,by omega,h1,h2⟩

/-- The small-frequency / large-label pair split also applies to
this new odd-position sampled word. -/
theorem odd_window_certificate_of_split {u B y W a : ℕ} (u1 : 0<u)
    (square : 7*(4*u)≤B*B)
    (travel : 4*(highSet B y).card*(2*B+3*lowModulus B y)<3*u-2)
    (budget : 2*u*(((highSet B y).filter (·≤W)).card*a) +
        (∑ M ∈ sources u, smallExcess W a (oddSampleAt B y M)) +
        (∑ M ∈ sources u, largePairs W (oddSampleAt B y M)) <
          2*u*(highSet B y).card) :
    ∃ p, 2*(4*u)-3≤p ∧ p.Prime ∧ (p+2).Prime := by
  apply odd_window_certificate u1 square travel
  have one (M : ℕ) : oddRepeatsAt B y M ≤
      ((highSet B y).filter (·≤W)).card*a +
      smallExcess W a (oddSampleAt B y M) +
      largePairs W (oddSampleAt B y M) := by
    apply split_count
    intro p hp hW
    have hm := sampleOdd_mem hp
    have hf := List.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨run_mem (canonical_spec B M) p hf.1, by simpa using hf.2⟩, hW⟩
  have hh := Finset.sum_le_sum (s:=sources u) (fun M _ => one M)
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hh
  have card : (sources u).card=2*u := by simp [sources]
  rw [card] at hh
  exact lt_of_le_of_lt hh budget

/-! The PR #8 one-donor high word p,q,p yields two matching samples. -/
theorem everyOther_pqp (p q : ℕ) (tail : List ℕ) :
    ∃ r, everyOther (p::q::p::tail) = p::p::r := by
  cases tail with
  | nil => exact ⟨[], rfl⟩
  | cons x xs => exact ⟨everyOther xs, rfl⟩

theorem sampleOdd_pqp (P p q : ℕ) (tail : List ℕ) (pos : 0<P) :
    ∃ r, sampleOdd P (p::q::p::tail) = p::p::r := by
  obtain ⟨r, hr⟩ := everyOther_pqp p q tail
  unfold sampleOdd
  rw [hr]
  cases P with
  | zero => omega
  | succ k =>
    refine ⟨r.take (2*k), ?_⟩
    have he : 2 * Nat.succ k = Nat.succ (Nat.succ (2*k)) := by omega
    rw [he]
    rfl

private theorem repeats_pp (p : ℕ) (w : List ℕ) :
    1 ≤ repeats (p::p::w) := by
  rw [repeats_eq_sum]
  have hp : p ∈ (p::p::w).toFinset := by simp
  have hcount : 2 ≤ (p::p::w).count p := by simp
  have hterm : 1 ≤ (p::p::w).count p-1 := by omega
  have hsum : (p::p::w).count p-1 ≤
      ∑ q ∈ (p::p::w).toFinset, ((p::p::w).count q-1) := by
    exact Finset.single_le_sum
      (s:=(p::p::w).toFinset)
      (f:=fun q => (p::p::w).count q-1)
      (fun q _ => Nat.zero_le _) hp
  omega

/-- Honest first-high p,q,p is *directly* a collision in the new sample,
unlike in the original every-third sample. -/
theorem first_three_high_pqp_implies_odd_repeat {B y M p q : ℕ}
    {tail : List ℕ}
    (hprefix : highWord y (canonical B M).1 = p::q::p::tail)
    (positive : 0 < (highSet B y).card) :
    1 ≤ oddRepeatsAt B y M := by
  unfold oddRepeatsAt oddSampleAt
  rw [hprefix]
  obtain ⟨rest,hr⟩ := sampleOdd_pqp (highSet B y).card p q tail positive
  rw [hr]
  exact repeats_pp p rest

#print axioms sampleOdd_lower
#print axioms nontwin_odd_lower
#print axioms odd_window_certificate
#print axioms unbounded_twins_of_odd_certificates
#print axioms odd_window_certificate_of_split
#print axioms first_three_high_pqp_implies_odd_repeat

end CanonicalMinPrefix
