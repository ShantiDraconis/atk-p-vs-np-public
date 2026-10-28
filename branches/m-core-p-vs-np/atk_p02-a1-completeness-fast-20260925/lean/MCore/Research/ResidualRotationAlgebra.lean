import Std

namespace MCore
namespace Research
namespace ResidualRotationAlgebra

/-- Pure research model: magnitude and orientation are carried separately so
orientation remains meaningful even when the residual magnitude reaches zero. -/
structure ResidualState where
  macroRadius : Int
  macroPhase : Int
  residualMagnitude : Nat
  residualPhase : Int
  deriving Repr, DecidableEq

/-- Integer-parameter residual rotation operator.  This file deliberately uses
only algebraic bookkeeping; no SAT/P02 theorem is imported here. -/
structure RotationOperator where
  macroScale : Int
  macroTurn : Int
  residualScale : Nat
  residualTurn : Int
  deriving Repr, DecidableEq

def apply (R : RotationOperator) (z : ResidualState) : ResidualState :=
  { macroRadius := R.macroScale * z.macroRadius
    macroPhase := z.macroPhase + R.macroTurn
    residualMagnitude := R.residualScale * z.residualMagnitude
    residualPhase := z.residualPhase + R.residualTurn }

def compose (R₂ R₁ : RotationOperator) : RotationOperator :=
  { macroScale := R₂.macroScale * R₁.macroScale
    macroTurn := R₁.macroTurn + R₂.macroTurn
    residualScale := R₂.residualScale * R₁.residualScale
    residualTurn := R₁.residualTurn + R₂.residualTurn }

theorem apply_compose
    (R₂ R₁ : RotationOperator)
    (z : ResidualState) :
    apply (compose R₂ R₁) z = apply R₂ (apply R₁ z) := by
  cases R₂
  cases R₁
  cases z
  simp [apply, compose, Int.mul_assoc, Nat.mul_assoc,
    Int.add_assoc, Int.mul_left_comm, Int.mul_comm]

/-- Orientation is an explicit state component and is therefore not erased by
zero residual magnitude in this research representation. -/
def sameResidualOrientation (a b : ResidualState) : Prop :=
  a.residualPhase = b.residualPhase

theorem zero_magnitude_preserves_explicit_orientation
    (a b : ResidualState)
    (ha : a.residualMagnitude = 0)
    (hb : b.residualMagnitude = 0)
    (hphase : a.residualPhase = b.residualPhase) :
    sameResidualOrientation a b := by
  exact hphase

/-
RESEARCH_ONLY / ZERO_PROOF_CREDIT.
This algebra does not imply G21, P02, or P ≠ NP.
Promotion is allowed only through a real semantic bridge to repository objects.
-/

end ResidualRotationAlgebra
end Research
end MCore
