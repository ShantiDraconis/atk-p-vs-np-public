import MCore.Real.P02TwoSidedExactnessAudit
import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace P02UniversalFailureWitnessMaterial

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open FailProofAllGaps
open P02TwoSidedExactnessAudit

abbrev CanonicalSAT : BitLanguage :=
  SATBits circuitBitEncoding

/-- A computational witness of universal failure must range over arbitrary
polynomial-time deterministic candidates. Quantifying PolyDTMRealization
CanonicalSAT here would already assume the candidate is correct on every input. -/
structure UniversalFailureWitness where
  counterexample : PolyDTMCandidate → BitString
  fails :
    ∀ M : PolyDTMCandidate,
      ¬ M.CorrectAt CanonicalSAT (counterexample M)

/-- This is exactly the repository's failure-generator payload for canonical SAT. -/
def UniversalFailureWitness.toFailureGenerator
    (W : UniversalFailureWitness) :
    FailureGenerator CanonicalSAT where
  counterexample := W.counterexample
  fails := W.fails

theorem witness_implies_universalFailure
    (W : UniversalFailureWitness) :
    UniversalFailure CanonicalSAT :=
  failure_generator_implies_universal_failure W.toFailureGenerator

theorem witness_implies_notInP
    (W : UniversalFailureWitness) :
    ¬ InP CanonicalSAT :=
  universal_failure_implies_not_in_p
    (witness_implies_universalFailure W)

theorem witness_implies_p_ne_np
    (W : UniversalFailureWitness) :
    PneqNP :=
  g2_proved_implies_p_ne_np
    (witness_implies_universalFailure W)

/-- Honest remaining lower-bound object. No inhabitant is asserted here. -/
def UNIVERSAL_FAILURE_WITNESS_OPEN_MATH : Prop :=
  Nonempty UniversalFailureWitness

/-- Exactness audit: this witness type is not an easier replacement for G2. -/
theorem witness_iff_universalFailure :
    Nonempty UniversalFailureWitness ↔
      UniversalFailure CanonicalSAT := by
  constructor
  · rintro ⟨W⟩
    exact witness_implies_universalFailure W
  · intro h
    exact ⟨
      { counterexample :=
          (failureGeneratorOfUniversalFailure h).counterexample
        fails :=
          (failureGeneratorOfUniversalFailure h).fails }⟩

#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.UniversalFailureWitness.toFailureGenerator
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_implies_universalFailure
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_implies_notInP
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_implies_p_ne_np
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_iff_universalFailure

end P02UniversalFailureWitnessMaterial
end Real
end MCore
