import MCore.Real.P02UniversalFailureAlgebra
import MCore.Real.P01FinalCertificate
import MCore.Real.CookNormalizedG3Contract
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace FinalTwoProducerSprint

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P01FinalCertificate
open P02UniversalFailureAlgebra
open CookNormalizedG3Contract
open FinalExternalCertificate

/-- Minimal exact P02 mathematical producer: for every candidate whose declared
clock is total, give one semantic mismatch. No auxiliary behavior layer needed. -/
structure TotalCandidateSeparationLaw where
  witness : PolyDTMCandidate → BitString
  separates :
    ∀ M, DeclaredClockTotal M → SemanticMismatch M (witness M)

/-- Reuse the already-proved clock/semantic dichotomy to obtain one concrete
counterexample for every deterministic polynomial-time candidate. -/
noncomputable def failureGeneratorOfSeparationLaw
    (L : TotalCandidateSeparationLaw) :
    FailProofAllGaps.FailureGenerator
      (SATBits circuitBitEncoding) := by
  classical
  refine
    { counterexample := fun M =>
        if hTotal : DeclaredClockTotal M then
          L.witness M
        else
          Classical.choose
            ((not_declaredClockTotal_iff_exists_clock_failure M).mp hTotal)
      fails := ?_ }
  intro M
  by_cases hTotal : DeclaredClockTotal M
  · simp [hTotal]
    have hMismatch : SemanticMismatch M (L.witness M) :=
      L.separates M hTotal
    exact
      (not_correctAt_iff_clock_or_semantic_mismatch
        M (L.witness M)).mpr (Or.inr hMismatch)
  · simp [hTotal]
    let x : BitString :=
      Classical.choose
        ((not_declaredClockTotal_iff_exists_clock_failure M).mp hTotal)
    have hx : ¬ DeclaredHalts M x :=
      Classical.choose_spec
        ((not_declaredClockTotal_iff_exists_clock_failure M).mp hTotal)
    exact
      (not_correctAt_iff_clock_or_semantic_mismatch M x).mpr
        (Or.inl hx)

/-- Exact two-producer payload after all reusable P02/G3 wiring is eliminated. -/
structure FinalTwoProducerInputs where
  p01 : P01MachineConstruction
  p02law : TotalCandidateSeparationLaw

noncomputable def FinalTwoProducerInputs.toExternalInputs
    (I : FinalTwoProducerInputs) :
    FinalExternalInputs where
  g1 := construction_closes_p01 ⟨I.p01⟩
  g2 := failureGeneratorOfSeparationLaw I.p02law
  g3 := cookNormalizedExternalContract

theorem final_two_producers_close_external
    (I : FinalTwoProducerInputs) :
    FailProofAllGaps.OfficialPneqNP
      cookNormalizedSelection.model.P
      cookNormalizedSelection.model.NP := by
  exact final_external_certificate I.toExternalInputs

def FinalTwoProducerGap : Prop :=
  Nonempty FinalTwoProducerInputs

#print axioms MCore.Real.FinalTwoProducerSprint.failureGeneratorOfSeparationLaw
#print axioms MCore.Real.FinalTwoProducerSprint.final_two_producers_close_external

end FinalTwoProducerSprint
end Real
end MCore
