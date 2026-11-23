import research.min_growing_cutoff
import Mathlib.Data.Nat.Prime.Basic

/-! The canonical clipped MIN wheel. Time advances to the first eligible tick,
and the least eligible prime wins a tie. All endpoints lie before the source's K. -/
set_option autoImplicit false
namespace CanonicalMinPrefix

def pool (B : ℕ) : Finset ℕ :=
  (Finset.range (B+1)).filter fun p => p.Prime ∧ p % 2 = 1

theorem mem_pool {B p : ℕ} : p ∈ pool B ↔ p ≤ B ∧ p.Prime ∧ p % 2 = 1 := by
  simp only [pool, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

def slot (n C p : ℕ) : Prop :=
  ((∃ k : ℕ, n = (2*p)*k) ∧ p ∣ C-1) ∨
  ((∃ k : ℕ, n = (2*p)*k+(p+2)) ∧ p ∣ C+1)

def active (B n C p : ℕ) : Prop := p ∈ pool B ∧ slot n C p

structure First (B t C n p : ℕ) : Prop where
  later : t < n
  hit : active B n C p
  earliest : ∀ u q, t < u → u < n → ¬active B u C q
  least : ∀ q, active B n C q → p ≤ q

inductive Run (B K : ℕ) : ℕ → ℕ → List ℕ → ℕ → Prop where
  | stop {t C} (quiet : ∀ n p, t < n → n ≤ K → ¬active B n C p) :
      Run B K t C [] C
  | step {t C n p w Z} (win : First B t C n p) (bound : n ≤ K)
      (tail : Run B K n (C + (p-1)) w Z) : Run B K t C (p::w) Z

theorem run_exists (B K t C : ℕ) : ∃ w Z, Run B K t C w Z := by
  classical
  by_cases h : ∃ n : ℕ, t < n ∧ n ≤ K ∧ ∃ p, active B n C p
  · let n := Nat.find h
    have hn : t < n ∧ n ≤ K ∧ ∃ p, active B n C p := Nat.find_spec h
    let p := Nat.find hn.2.2
    have hp : active B n C p := Nat.find_spec hn.2.2
    obtain ⟨w, Z, tail⟩ := run_exists B K n (C + (p-1))
    refine ⟨p::w, Z, Run.step ⟨hn.1, hp, ?_, ?_⟩ hn.2.1 tail⟩
    · intro u q hu hu' hq
      have hh : n ≤ u := Nat.find_min' h ⟨hu, by omega, q, hq⟩
      omega
    · intro q hq
      exact Nat.find_min' hn.2.2 hq
  · exact ⟨[], C, Run.stop fun n p hn hk hp => h ⟨n, hn, hk, p, hp⟩⟩
termination_by K-t
decreasing_by omega

theorem first_unique {B t C n p u q : ℕ} (a : First B t C n p)
    (b : First B t C u q) : n = u ∧ p = q := by
  have h₁ : ¬n<u := fun h => b.earliest n p a.later h a.hit
  have h₂ : ¬u<n := fun h => a.earliest u q b.later h b.hit
  have e : n=u := by omega
  subst u
  exact ⟨rfl, Nat.le_antisymm (a.least _ b.hit) (b.least _ a.hit)⟩

theorem run_unique {B K t C : ℕ} {w v : List ℕ} {Z Y : ℕ}
    (h : Run B K t C w Z) (h' : Run B K t C v Y) : w=v ∧ Z=Y := by
  induction h generalizing v Y with
  | stop quiet =>
    cases h' with
    | stop => exact ⟨rfl,rfl⟩
    | step win bound _ => exact (quiet _ _ win.later bound win.hit).elim
  | step win bound _ ih =>
    cases h' with
    | stop quiet => exact (quiet _ _ win.later bound win.hit).elim
    | step win' _ tail' =>
      obtain ⟨rfl,rfl⟩ := first_unique win win'
      obtain ⟨rfl,rfl⟩ := ih tail'
      exact ⟨rfl,rfl⟩

private theorem next_residue (t m r : ℕ) (hm : 0<m) (hr : r<m) :
    ∃ k : ℕ, t < m*k+r ∧ m*k+r ≤ t+m := by
  have he := Nat.mod_add_div t m
  have hl := Nat.mod_lt t hm
  by_cases h : t%m < r
  · exact ⟨t/m, by omega, by omega⟩
  · refine ⟨t/m+1, ?_, ?_⟩ <;> rw [Nat.mul_add, Nat.mul_one] <;> omega

theorem clock_hit {B t C p : ℕ} (hp : p ∈ pool B) (h : p ∣ C-1 ∨ p ∣ C+1) :
    ∃ n, t<n ∧ n≤t+2*p ∧ active B n C p := by
  have hm := mem_pool.mp hp
  have hp2 := hm.2.1.two_le
  rcases h with h | h
  · obtain ⟨k, hk, hk'⟩ := next_residue t (2*p) 0 (by omega) (by omega)
    exact ⟨_, by simpa using hk, by simpa using hk', hp, Or.inl ⟨⟨k,rfl⟩,h⟩⟩
  · obtain ⟨k,hk,hk'⟩ := next_residue t (2*p) (p+2) (by omega) (by omega)
    exact ⟨_, hk, hk', hp, Or.inr ⟨⟨k,rfl⟩,h⟩⟩

theorem First.gap {B t C n p : ℕ} (w : First B t C n p) : n≤t+2*p := by
  have hd : p ∣ C-1 ∨ p ∣ C+1 := w.hit.2.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  obtain ⟨u, hu, hu', hit⟩ := clock_hit (t:=t) w.hit.1 hd
  by_contra! h
  exact w.earliest u p hu (by omega) hit

def highSet (B y : ℕ) := (pool B).filter fun p => y < p

def highWord (y : ℕ) (w : List ℕ) := w.filter fun p => y < p

/-- Starting with the third item, retain every third one. -/
def thirds : List ℕ → List ℕ
  | _ :: _ :: p :: tail => p :: thirds tail
  | _ => []

theorem thirds_length (w : List ℕ) : (thirds w).length = w.length / 3 := by
  fun_induction thirds w <;> simp_all [List.length_cons] <;> omega

theorem thirds_mem {p : ℕ} {w : List ℕ} (h : p ∈ thirds w) : p ∈ w := by
  induction w using thirds.induct with
  | case1 a b c tail ih =>
    simp only [thirds, List.mem_cons] at h ⊢
    rcases h with e | h
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (ih h)))
  | case2 => simp [thirds] at h
  | case3 => simp [thirds] at h
  | case4 => simp [thirds] at h

def sample (P : ℕ) (w : List ℕ) := thirds (w.take (6*P))

def repeats (w : List ℕ) := w.length - w.toFinset.card

theorem sampled_lower {P : ℕ} {S : Finset ℕ} {w : List ℕ}
    (card : S.card = P) (allowed : ∀ p ∈ w, p ∈ S) (long : 6*P ≤ w.length) :
    P ≤ repeats (sample P w) := by
  have hs : (sample P w).toFinset ⊆ S := by
    intro p hp
    exact allowed p (List.mem_of_mem_take (thirds_mem (List.mem_toFinset.mp hp)))
  have hle := Finset.card_le_card hs
  have hlen : (sample P w).length = 2*P := by
    rw [sample, thirds_length, List.length_take, Nat.min_eq_left long]
    omega
  unfold repeats
  omega

#print axioms run_exists
#print axioms run_unique
#print axioms First.gap
#print axioms sampled_lower
end CanonicalMinPrefix
