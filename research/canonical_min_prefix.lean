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

theorem thirds_length : ∀ w : List ℕ, (thirds w).length = w.length / 3
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: t => by
    simp only [thirds, List.length_cons, thirds_length t]
    omega

theorem thirds_mem {p : ℕ} {w : List ℕ} (h : p ∈ thirds w) : p ∈ w := by
  induction w using thirds.induct with
  | case1 a b c tail ih =>
    simp only [thirds, List.mem_cons] at h ⊢
    rcases h with e | h
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (ih h)))
  | case2 => simp [thirds] at h

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

/-- For the original odd/even clock, eligible labels are exactly the odd
primes dividing the appropriate parity GCD. -/
theorem active_iff_gcd {B n C p : ℕ} (hn : 3 ≤ n) :
    active B n C p ↔ p ∈ pool B ∧
      ((n % 2 = 0 ∧ p ∣ Nat.gcd n (C-1)) ∨
       (n % 2 = 1 ∧ p ∣ Nat.gcd (n-2) (C+1))) := by
  constructor
  · rintro ⟨hp, hs⟩
    have hodd := (mem_pool.mp hp).2.2
    refine ⟨hp, ?_⟩
    rcases hs with ⟨⟨k, hk⟩, hd⟩ | ⟨⟨k, hk⟩, hd⟩
    · have e : n = 2*(p*k) := by rw [hk]; ring
      refine Or.inl ⟨by omega, Nat.dvd_gcd ⟨2*k, ?_⟩ hd⟩
      rw [hk]; ring
    · have e : n = 2*(p*k) + p + 2 := by rw [hk]; ring
      refine Or.inr ⟨by omega, Nat.dvd_gcd ⟨2*k+1, ?_⟩ hd⟩
      have : n = p*(2*k+1)+2 := by rw [hk]; ring
      omega
  · rintro ⟨hp, hs⟩
    have hodd := (mem_pool.mp hp).2.2
    refine ⟨hp, ?_⟩
    rcases hs with ⟨he, hd⟩ | ⟨he, hd⟩
    · obtain ⟨k, hk⟩ := dvd_trans hd (Nat.gcd_dvd_left _ _)
      refine Or.inl ⟨⟨k/2, ?_⟩, dvd_trans hd (Nat.gcd_dvd_right _ _)⟩
      have hmod : (p*k)%2 = k%2 := by rw [Nat.mul_mod, hodd, Nat.one_mul, Nat.mod_mod]
      have ke : 2*(k/2)=k := by omega
      calc n = p*k := hk
           _ = p*(2*(k/2)) := congrArg (p*·) ke.symm
           _ = (2*p)*(k/2) := by ring
    · obtain ⟨k, hk⟩ := dvd_trans hd (Nat.gcd_dvd_left _ _)
      refine Or.inr ⟨⟨k/2, ?_⟩, dvd_trans hd (Nat.gcd_dvd_right _ _)⟩
      have hmod : (p*k)%2 = k%2 := by rw [Nat.mul_mod, hodd, Nat.one_mul, Nat.mod_mod]
      have ke : 2*(k/2)+1=k := by omega
      calc n = p*k+2 := by omega
           _ = p*(2*(k/2)+1)+2 := congrArg (fun x => p*x+2) ke.symm
           _ = (2*p)*(k/2)+(p+2) := by ring

private theorem update_bound {B t C n p : ℕ} (w : First B t C n p)
    (ht : 2≤t) (hC : 4≤C) (even : C%2=0) (bound : C≤2*t) :
    C+(p-1) ≤ 2*n := by
  have hn := w.later
  rcases (active_iff_gcd (by omega : 3≤n)).mp w.hit with ⟨_, h⟩
  rcases h with ⟨_,hd⟩ | ⟨_,hd⟩
  · have hd₁ := dvd_trans hd (Nat.gcd_dvd_left _ _)
    have hd₂ := dvd_trans hd (Nat.gcd_dvd_right _ _)
    have hmul : p ∣ 2*n := dvd_mul_of_dvd_right hd₁ 2
    have hs := Nat.le_of_dvd (by omega : 0<2*n-(C-1)) (Nat.dvd_sub hmul hd₂)
    omega
  · have hd₁ := dvd_trans hd (Nat.gcd_dvd_left _ _)
    have hd₂ := dvd_trans hd (Nat.gcd_dvd_right _ _)
    have hmul : p ∣ 2*(n-2) := dvd_mul_of_dvd_right hd₁ 2
    by_cases k : C+1 < 2*(n-2)
    · have hs := Nat.le_of_dvd (by omega : 0<2*(n-2)-(C+1)) (Nat.dvd_sub hmul hd₂)
      omega
    · have hs := Nat.le_of_dvd (by omega : 0<C+1-2*(n-2)) (Nat.dvd_sub hd₂ hmul)
      omega

def Twin (C : ℕ) : Prop := (C-1).Prime ∧ (C+1).Prime

private theorem composite_factor {B z : ℕ} (hz : 2≤z) (ho : z%2=1)
    (hs : z<B*B) (hc : ¬z.Prime) :
    ∃ p ∈ pool B, p ∣ z := by
  let p := z.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hd : p ∣ z := Nat.minFac_dvd z
  have hsq := Nat.minFac_sq_le_self (by omega : 0<z) hc
  change p^2 ≤ z at hsq
  have hle : p≤B := by by_contra! hh; nlinarith [Nat.mul_self_le_mul_self hh.le]
  have hodd : p%2=1 := hp.eq_two_or_odd.elim
    (fun h => by rw [h] at hd; omega) id
  exact ⟨p, mem_pool.mpr ⟨hle,hp,hodd⟩,hd⟩

private theorem barrier_exists (C L : ℕ) (hL : 0<L) (he : L%2=0) :
    ∃ J, L ∣ J ∧ J%2=0 ∧ C≤J ∧ J≤C+L := by
  refine ⟨L*(C/L+1), ⟨_,rfl⟩, ?_, ?_, ?_⟩
  · rw [Nat.mul_mod, he]; simp
  all_goals
    rw [Nat.mul_add, Nat.mul_one]
    have hm := Nat.mod_add_div C L
    have hr := Nat.mod_lt C hL
    omega

private theorem bounded_phase {B K t C Z y L : ℕ} {w : List ℕ}
    (run : Run B K t C w Z) (cut : ∀ p ∈ pool B, p≤y → p ∣ L)
    (pos : 0<L) (evenL : L%2=0) (square : 2*K+1<B*B) (bad : ¬Twin Z)
    (ht : 2≤t) (tK : t≤K) (hC : 4≤C) (even : C%2=0) (bound : C≤2*t)
    (J : ℕ) (hLJ : L ∣ J) (evenJ : J%2=0) (before : C≤J) :
    K≤t+(highWord y w).length*(2*B+3*L)+2*B+3*(J-C) := by
  induction run generalizing J with
  | @stop t C quiet =>
    have hf : ∃ p ∈ pool B, p ∣ C-1 ∨ p ∣ C+1 := by
      by_cases left : (C-1).Prime
      · have hh : ¬(C+1).Prime := fun h => bad ⟨left,h⟩
        obtain ⟨p,hp,hd⟩ := composite_factor (B:=B) (z:=C+1)
          (by omega) (by omega) (by omega) hh
        exact ⟨p,hp,Or.inr hd⟩
      · obtain ⟨p,hp,hd⟩ := composite_factor (B:=B) (z:=C-1)
          (by omega) (by omega) (by omega) left
        exact ⟨p,hp,Or.inl hd⟩
    obtain ⟨p,hp,hd⟩ := hf
    obtain ⟨n,hn,hg,hit⟩ := clock_hit (t:=t) hp hd
    have hpb := (mem_pool.mp hp).1
    have hnk : K<n := by by_contra! h; exact quiet n p hn h hit
    simp [highWord]
    omega
  | @step t C n p w Z win nk tail ih =>
    have np := win.later
    have hpool := win.hit.1
    have hm := mem_pool.mp hpool
    have hp2 := hm.2.1.two_le
    have pgap := win.gap
    have cb := update_bound win ht hC even bound
    have c2 : 4≤C+(p-1) := by omega
    have ev' : (C+(p-1))%2=0 := by omega
    by_cases low : p≤y
    · have hd : p ∣ C-1 ∨ p ∣ C+1 :=
        win.hit.2.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
      have hb := MinGrowingCutoff.even_barrier (by omega : 2≤C) before even evenJ
        hm.2.2 (dvd_trans (cut p hpool low) hLJ) hd
      have rest := ih bad (by omega) nk c2 ev' cb J hLJ evenJ hb
      have small : ¬y<p := by omega
      have len : (highWord y (p::w)).length = (highWord y w).length := by simp [highWord, small]
      rw [len]
      omega
    · obtain ⟨J',div',even',start',close'⟩ := barrier_exists (C+(p-1)) L pos evenL
      have rest := ih bad (by omega) nk c2 ev' cb J' div' even' start'
      have large : y<p := by omega
      have len : (highWord y (p::w)).length = (highWord y w).length+1 := by simp [highWord, large]
      rw [len, Nat.add_mul, Nat.one_mul]
      omega

theorem clock_budget {B K t C Z y L : ℕ} {w : List ℕ} (run : Run B K t C w Z)
    (cut : ∀ p ∈ pool B, p≤y → p ∣ L) (pos : 0<L) (evenL : L%2=0)
    (square : 2*K+1<B*B) (bad : ¬Twin Z) (ht : 2≤t) (tK : t≤K)
    (hC : 4≤C) (even : C%2=0) (bound : C≤2*t) :
    K-t ≤ ((highWord y w).length+1)*(2*B+3*L) := by
  obtain ⟨J,hLJ,evenJ,before,close⟩ := barrier_exists C L pos evenL
  have h := bounded_phase run cut pos evenL square bad ht tK hC even bound
    J hLJ evenJ before
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem run_mem {B K t C Z : ℕ} {w : List ℕ} (h : Run B K t C w Z) :
    ∀ p ∈ w, p ∈ pool B := by
  induction h with
  | stop => simp
  | step win _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact win.hit.1
    · exact ih _ hp

def start (M : ℕ) := M+2
def initial (M : ℕ) := 2*M-2
def finish (M : ℕ) := (7*M-1)/4

noncomputable def canonical (B M : ℕ) : List ℕ × ℕ :=
  let w := Classical.choose (run_exists B (finish M) (start M) (initial M))
  (w, Classical.choose (Classical.choose_spec (run_exists B (finish M) (start M) (initial M))))

theorem canonical_spec (B M : ℕ) :
    Run B (finish M) (start M) (initial M) (canonical B M).1 (canonical B M).2 := by
  exact Classical.choose_spec (Classical.choose_spec (run_exists B (finish M) (start M) (initial M)))

noncomputable def repeatsAt (B y M : ℕ) : ℕ :=
  repeats (sample (highSet B y).card (highWord y (canonical B M).1))

theorem nontwin_sample_lower {B y L M : ℕ} (hM : 5≤M)
    (cut : ∀ p ∈ pool B, p≤y → p ∣ L) (pos : 0<L) (evenL : L%2=0)
    (square : 2*finish M+1<B*B)
    (travel : 6*(highSet B y).card*(2*B+3*L) < finish M - start M)
    (bad : ¬Twin (canonical B M).2) :
    (highSet B y).card ≤ repeatsAt B y M := by
  have run := canonical_spec B M
  have bud := clock_budget run cut pos evenL square bad
    (by simp [start]) (by unfold start finish; omega) (by unfold initial; omega)
    (by unfold initial; omega) (by unfold start initial; omega)
  have hl : 6*(highSet B y).card ≤ (highWord y (canonical B M).1).length := by
    by_contra! h
    have hm := Nat.mul_le_mul_right (2*B+3*L) (by omega :
      (highWord y (canonical B M).1).length+1 ≤ 6*(highSet B y).card)
    omega
  apply sampled_lower (S:=highSet B y) rfl _ hl
  intro p hp
  have hh := List.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨run_mem run p hh.1, by simpa using hh.2⟩

theorem twin_of_sample_deficit {B y L : ℕ} (sources : Finset ℕ)
    (cut : ∀ p ∈ pool B, p≤y → p ∣ L) (pos : 0<L) (evenL : L%2=0)
    (bounds : ∀ M ∈ sources, 5≤M ∧ 2*finish M+1<B*B ∧
      6*(highSet B y).card*(2*B+3*L)<finish M-start M)
    (deficit : (∑ M ∈ sources, repeatsAt B y M) < sources.card*(highSet B y).card) :
    ∃ M ∈ sources, Twin (canonical B M).2 := by
  classical
  by_contra! bad
  have lower := Finset.sum_le_sum (s:=sources) (fun M hM =>
    nontwin_sample_lower (bounds M hM).1 cut pos evenL (bounds M hM).2.1
      (bounds M hM).2.2 (bad M hM))
  have hlow : sources.card*(highSet B y).card ≤ ∑ M ∈ sources, repeatsAt B y M := by simpa using lower
  exact (not_lt_of_ge hlow) deficit

#print axioms active_iff_gcd
#print axioms clock_budget
#print axioms nontwin_sample_lower
#print axioms twin_of_sample_deficit

end CanonicalMinPrefix
