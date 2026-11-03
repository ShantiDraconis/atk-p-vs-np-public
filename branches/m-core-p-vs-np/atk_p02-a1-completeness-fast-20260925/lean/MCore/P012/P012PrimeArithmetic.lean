import Std

namespace MCore
namespace P012

/-- Finite trial-division checker used by the P012/Prime2 research layer.
It is deliberately computational and has no dependency on Mathlib. -/
def primeCheck (n : Nat) : Bool :=
  (List.range n).all (fun d =>
    if 2 ≤ d then decide (n % d ≠ 0) else true)

/-- Standard finite primality specification used in this research layer:
n is at least 2 and has no divisor d with 2 ≤ d < n. -/
def PrimeNat (n : Nat) : Prop :=
  2 ≤ n ∧ primeCheck n = true

instance instDecidablePrimeNat (n : Nat) : Decidable (PrimeNat n) := by
  unfold PrimeNat
  infer_instance

theorem primeNat_two_le {n : Nat} (h : PrimeNat n) : 2 ≤ n :=
  h.1

theorem primeNat_two : PrimeNat 2 := by
  decide

theorem primeNat_three : PrimeNat 3 := by
  decide

theorem primeNat_five : PrimeNat 5 := by
  decide

theorem not_primeNat_zero : ¬ PrimeNat 0 := by
  decide

theorem not_primeNat_one : ¬ PrimeNat 1 := by
  decide

theorem not_primeNat_four : ¬ PrimeNat 4 := by
  decide

end P012
end MCore
