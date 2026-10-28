import MCore.Real.P02BoundedFinalBridge

namespace MCore
namespace Real
namespace P02BoundedOpenMath

open CanonicalFinalProof
open CanonicalCircuitBits
open P02BoundedSemanticInput
open P02CookLevinFromBoundedExec
open P02BoundedFinalBridge

/--
Terminal OPEN_MATH statement for the bounded lane.

For every polynomial deterministic candidate M, there is a finite fuel and
recursion-theoretic code c whose bounded semantic input is exactly the
canonical Cook-Levin rejection circuit built from that same bounded input.

This is the bounded same-input equation.  It is not inhabited here.
-/
def BoundedSameInputEquation : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ fuel : Nat, ∃ code : Nat.Partrec.Code,
      selfInputFuel fuel code =
        encodeCircuit
          (rejectCircuit M (selfInputFuel fuel code))

/-- The equation is exactly the repository's terminal bounded producer. -/
theorem boundedSameInputEquation_iff_producer :
    BoundedSameInputEquation ↔ UniformBoundedSameInputProducer := by
  constructor
  · intro h M
    rcases h M with ⟨fuel, code, hsame⟩
    exact ⟨{
      fuel := fuel
      code := code
      same_input := hsame
    }⟩
  · intro h M
    rcases h M with ⟨W⟩
    exact ⟨W.fuel, W.code, W.same_input⟩

/-- One-candidate form, useful for attacking the theorem pointwise. -/
def BoundedSameInputAt (M : PolyDTMCandidate) : Prop :=
  ∃ fuel : Nat, ∃ code : Nat.Partrec.Code,
    selfInputFuel fuel code =
      encodeCircuit
        (rejectCircuit M (selfInputFuel fuel code))

theorem boundedSameInputAt_iff
    (M : PolyDTMCandidate) :
    BoundedSameInputAt M ↔ Nonempty (BoundedSameInputWitness M) := by
  constructor
  · rintro ⟨fuel, code, hsame⟩
    exact ⟨{
      fuel := fuel
      code := code
      same_input := hsame
    }⟩
  · rintro ⟨W⟩
    exact ⟨W.fuel, W.code, W.same_input⟩

/-- Uniform closure is exactly pointwise closure for every candidate. -/
theorem producer_iff_pointwise :
    UniformBoundedSameInputProducer ↔
      ∀ M : PolyDTMCandidate, BoundedSameInputAt M := by
  constructor
  · intro h M
    exact (boundedSameInputAt_iff M).2 (h M)
  · intro h M
    exact (boundedSameInputAt_iff M).1 (h M)

/--
OPEN_MATH endpoint.

Any future proof should inhabit this theorem using only kernel-checked derivations.
Once inhabited, P02BoundedFinalBridge already promotes it to D3, P02 and the
external certificate chain.
-/
def OPEN_MATH_BOUNDED_SAME_INPUT : Prop :=
  BoundedSameInputEquation

theorem openMath_to_P02
    (h : OPEN_MATH_BOUNDED_SAME_INPUT) :
    P02TerminalFrontier.P02Target := by
  apply uniformBoundedSameInput_closes_P02
  exact boundedSameInputEquation_iff_producer.mp h

#print axioms MCore.Real.P02BoundedOpenMath.boundedSameInputEquation_iff_producer
#print axioms MCore.Real.P02BoundedOpenMath.boundedSameInputAt_iff
#print axioms MCore.Real.P02BoundedOpenMath.producer_iff_pointwise
#print axioms MCore.Real.P02BoundedOpenMath.openMath_to_P02

end P02BoundedOpenMath
end Real
end MCore
