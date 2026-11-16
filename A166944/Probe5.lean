import A166944.Lemmas
namespace A166944Research
example {q : Nat} (h : q ∣ 1) : q = 1 := by
  have hle : q ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) h
  omega
example {q : Nat} (hq : 1 < q) (h : q ∣ 1) : False := by
  have hle : q ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) h
  omega
example {q : Nat} (h : q ∣ 1) : q ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) h
example {q n : Nat} (hn : 0 < n) (h : q ∣ n) : q ≤ n := Nat.le_of_dvd hn h
end A166944Research
