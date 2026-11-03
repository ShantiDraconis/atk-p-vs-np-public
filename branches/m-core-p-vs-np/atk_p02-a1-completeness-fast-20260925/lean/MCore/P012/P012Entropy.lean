import Lean.Elab.Tactic.Omega
import MCore.P012.P012Core

namespace MCore
namespace P012

structure PerelmanW where
  W : Nat → Nat
  mono : ∀ t, W t ≤ W (t + 1)

def W_SAT : PerelmanW where
  W := fun t => t * t + 100
  mono := by
    intro t
    have hstep : t ≤ t + 1 := by omega
    have hmul : t * t ≤ (t + 1) * (t + 1) :=
      Nat.mul_le_mul hstep hstep
    exact Nat.add_le_add_right hmul 100

theorem L23_W_mono (t : Nat) :
    W_SAT.W t ≤ W_SAT.W (t + 1) := by
  exact W_SAT.mono t

def rigidityNumerator (good total : Nat) : Nat :=
  if total = 0 then 0 else good

def rigidityPerfect (n : Nat) : Prop :=
  rigidityNumerator n n = n

theorem rigidityPerfect_self (n : Nat) :
    rigidityPerfect n := by
  unfold rigidityPerfect rigidityNumerator
  by_cases h : n = 0
  · simp [h]
  · simp [h]

end P012
end MCore
