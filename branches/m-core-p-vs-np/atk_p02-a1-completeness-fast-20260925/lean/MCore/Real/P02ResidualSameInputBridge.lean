import MCore.Research.ResidualRotationAlgebra
import MCore.Real.P02KleeneCookLevinBridge

namespace MCore
namespace Real
namespace P02ResidualSameInputBridge

open CanonicalCircuitBits
open P02KleeneBridge
open P02KleeneCookLevinBridge
open MCore.Research.ResidualRotationAlgebra

/-- A research-to-real interface.  No theorem below constructs this interface;
it only states the exact data that would be required for residual orientation
to earn proof credit in the P02 chain. -/
structure ResidualSameInputInvariant
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M)
    (D : CookLevinSameInputData M K) where
  stateOf : Nat.Partrec.Code → ResidualState

  code_semantics_preserves_orientation :
    ∀ c,
      Nat.Partrec.Code.eval c = K.f c →
      sameResidualOrientation (stateOf c) (stateOf c)

  orientation_forces_same_input :
    ∀ c,
      Nat.Partrec.Code.eval c = K.f c →
      sameResidualOrientation (stateOf c) (stateOf c) →
      D.selfInput c = encodeCircuit (D.circuitOf c)

/-- Exact target: residual orientation may contribute only by proving the
existing same-input obligation. -/
theorem residualOrientation_to_same_input_of_fixed
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    {D : CookLevinSameInputData M K}
    (R : ResidualSameInputInvariant M K D) :
    ∀ c,
      Nat.Partrec.Code.eval c = K.f c →
      D.selfInput c = encodeCircuit (D.circuitOf c) := by
  intro c hfixed
  exact R.orientation_forces_same_input c hfixed
    (R.code_semantics_preserves_orientation c hfixed)

/-- Once same-input is obtained this way, the existing Cook-Levin bridge
produces flips_of_fixed without changing the terminal proposition. -/
theorem residualOrientation_to_flips_of_fixed
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    {D : CookLevinSameInputData M K}
    (R : ResidualSameInputInvariant M K D)
    (c : Nat.Partrec.Code)
    (hfixed : Nat.Partrec.Code.eval c = K.f c) :
    SATTarget (D.bitsOf c) ↔
      ¬ AcceptsAtDeclaredBound M (D.bitsOf c) := by
  have hsame :
      D.selfInput c = encodeCircuit (D.circuitOf c) :=
    residualOrientation_to_same_input_of_fixed R c hfixed
  simpa [CookLevinSameInputData.bitsOf, hsame] using
    D.cook_levin_correct c

/-
FAIL-CLOSED:
- residual algebra: research only;
- this file contributes proof credit only if ResidualSameInputInvariant is
  constructed from existing code/execution/circuit data without oracle fields;
- cook_levin_correct remains an independent OPEN_MATH obligation.
-/

#print axioms MCore.Real.P02ResidualSameInputBridge.residualOrientation_to_same_input_of_fixed
#print axioms MCore.Real.P02ResidualSameInputBridge.residualOrientation_to_flips_of_fixed

end P02ResidualSameInputBridge
end Real
end MCore
