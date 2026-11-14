/-
# Kernel-checked twin-primality of the records, and agreement with OEIS A166945 — self-contained, kernel-checked bounded verification.
No imports, no Mathlib. No sorry / admit / axiom / unsafe / native_decide.
-/
namespace A166944Research

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-- A166944: a(1)=2; a(n)=a(n-1)+gcd(n,a(n-1)) for even n, a(n)=a(n-1)+gcd(n-2,a(n-1)) for odd n. -/
def A : Nat → Nat
  | 0 => 0
  | 1 => 2
  | n + 2 => A (n + 1) + Nat.gcd (if (n + 2) % 2 = 0 then n + 2 else n) (A (n + 1))

/-- first difference d(n) = a(n) - a(n-1) -/
def d (n : Nat) : Nat := A n - A (n - 1)

/-- trial-division primality test (odd k, k*k > n stops) -/
def isPrimeB (n : Nat) : Bool :=
  if n < 2 then false
  else if n % 2 = 0 then n = 2
  else
    let rec go (fuel k : Nat) : Bool :=
      match fuel with
      | 0 => false
      | f + 1 => if k * k > n then true else if n % k = 0 then false else go f (k + 2)
    go n 3

/-- forward scan of d(2..N), keeping (n, d n) exactly when d n strictly exceeds the running maximum -/
def scan (N : Nat) : List (Nat × Nat) :=
  let rec go (fuel n a mx : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    match fuel with
    | 0 => acc
    | f + 1 =>
        let m := if n % 2 = 0 then n else n - 2
        let x := Nat.gcd m a
        if mx < x then go f (n + 1) (a + x) x ((n, x) :: acc)
        else go f (n + 1) (a + x) mx acc
  (go (N - 1) 2 2 1 []).reverse

/-- the conjecture's content over the computed record list: every record with 5 < R is a twin-prime greater member -/
def allTwinUpTo (N : Nat) : Bool :=
  (scan N).all (fun p => if 5 < p.2 then isPrimeB p.2 && isPrimeB (p.2 - 2) else true)

/-- OEIS A166945 first 21 terms (independently recomputed by Python for n <= 1e7) -/
def oeis21 : List (Nat × Nat) :=
  [(2, 2), (5, 3), (9, 7), (15, 13), (45, 43), (141, 139), (315, 313), (663, 661),
   (1323, 1321), (2661, 2659), (5421, 5419), (10893, 10891), (22041, 22039),
   (44385, 44383), (88803, 88801), (177843, 177841), (355725, 355723), (713835, 713833),
   (1427751, 1427749), (2860773, 2860771), (5725455, 5725453)]

def oeisUpTo (N : Nat) : List (Nat × Nat) := (oeis21.filter (fun p => p.1 ≤ N))

/-- kernel-checked (decide = kernel reduction) stages, increasing N -/
theorem t3000 : scan 3000 = oeisUpTo 3000 := by decide
theorem tw3000 : allTwinUpTo 3000 = true := by decide

end A166944Research
