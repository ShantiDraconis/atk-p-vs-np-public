import MCore.Real.CanonicalSATParserMachine
import MCore.Real.CanonicalSATSlotParserSpec

namespace MCore
namespace Real
namespace CanonicalSATRecursiveParserBudget

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATSlotParserSpec

theorem nat_pow_one_local (x : Nat) : x ^ 1 = x :=
  Nat.pow_one x

theorem nat_pow_two_local (x : Nat) : x ^ 2 = x * x := by
  rw [show (2 : Nat) = Nat.succ 1 by rfl]
  rw [Nat.pow_succ, Nat.pow_one]

/-- Every successfully parsed constructor head consumes at least three source
bits. INPUT may consume more because of its unary payload. -/
theorem head_encode_length_ge_three
    (h : Head) :
    3 ≤ h.encode.length := by
  cases h with
  | input i =>
      simp [Head.encode]
  | const b =>
      cases b <;> decide
  | not => decide
  | and => decide
  | or => decide

/-- Conservative budget for one parser macro-iteration (one constructor head,
its slot-log update, and rewind to the next unread source bit). -/
def macroIterationBound : TimeBound :=
  fun n => 16 * (n + 1)

/-- The macro budget is polynomial. -/
theorem macroIterationBound_poly :
    PolynomialTimeBound macroIterationBound := by
  refine ⟨16, 1, ?_⟩
  intro n
  unfold macroIterationBound
  rw [Nat.pow_one]
  exact Nat.le_refl _

/-- At most n+1 macro iterations can occur on an n-bit source because every
successful iteration consumes at least one source bit; malformed paths halt
earlier. This coarse count intentionally avoids relying on a tighter 3-bit
constructor estimate. -/
def macroIterationCountBound (n : Nat) : Nat :=
  n + 1

/-- Initialization plus all coarse macro iterations fit well inside the global
parserTimeBound = 256*(n+1)^2. -/
theorem global_budget_dominates
    (n : Nat) :
    (2 * n + 4) +
        macroIterationCountBound n * macroIterationBound n
      ≤ parserTimeBound n := by
  unfold macroIterationCountBound macroIterationBound parserTimeBound
  have hbase : 2 * n + 4 ≤ 4 * (n + 1) := by omega
  have hlin : 4 * (n + 1) ≤ 4 * (n + 1) ^ 2 := by
    have hp : 1 ≤ n + 1 := by omega
    have hs : n + 1 ≤ (n + 1) ^ 2 := by
      calc
        n + 1 = 1 * (n + 1) := by simp
        _ ≤ (n + 1) * (n + 1) :=
          Nat.mul_le_mul_right (n + 1) hp
        _ = (n + 1) ^ 2 := by
          rw [nat_pow_two_local]
    exact Nat.mul_le_mul_left 4 hs
  have hiter :
      (n + 1) * (16 * (n + 1)) =
        16 * (n + 1) ^ 2 := by
    rw [nat_pow_two_local]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hiter]
  calc
    2 * n + 4 + 16 * (n + 1) ^ 2
        ≤ 4 * (n + 1) ^ 2 + 16 * (n + 1) ^ 2 := by
            exact Nat.add_le_add_right (Nat.le_trans hbase hlin) _
    _ = 20 * (n + 1) ^ 2 := by omega
    _ ≤ 256 * (n + 1) ^ 2 := by
      exact Nat.mul_le_mul_right ((n + 1) ^ 2) (by decide)

/-- A convenient remaining-fuel form used by the eventual simulation
induction. -/
theorem one_iteration_plus_rest_fits
    (n k : Nat)
    (hk : k ≤ n + 1) :
    (2 * n + 4) + k * macroIterationBound n
      ≤ parserTimeBound n := by
  calc
    (2 * n + 4) + k * macroIterationBound n
        ≤ (2 * n + 4) +
            macroIterationCountBound n * macroIterationBound n := by
              apply Nat.add_le_add_left
              exact Nat.mul_le_mul_right _ hk
    _ ≤ parserTimeBound n := global_budget_dominates n

#print axioms MCore.Real.CanonicalSATRecursiveParserBudget.head_encode_length_ge_three
#print axioms MCore.Real.CanonicalSATRecursiveParserBudget.macroIterationBound_poly
#print axioms MCore.Real.CanonicalSATRecursiveParserBudget.global_budget_dominates
#print axioms MCore.Real.CanonicalSATRecursiveParserBudget.one_iteration_plus_rest_fits

end CanonicalSATRecursiveParserBudget
end Real
end MCore
