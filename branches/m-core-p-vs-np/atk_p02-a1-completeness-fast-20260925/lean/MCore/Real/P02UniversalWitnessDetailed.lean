import MCore.Real.P02SameInputClosure
import MCore.Real.P02UniversalWitnessChain

namespace MCore
namespace Real
namespace P02UniversalWitnessDetailed

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open FailProofAllGaps
open P02DiagonalFrontier
open P02SameInputClosure
open P02G21G22Attack

/-- Candidate-indexed semantic witness family. This is stronger data than bare
G21 because it records canonical validity and the explicit flip law. -/
structure UniversalWitnessFamily where
  witness :
    ∀ M : PolyDTMCandidate,
      DiagonalCounterexampleWitness M

def UniversalWitnessFamilyGap : Prop :=
  Nonempty UniversalWitnessFamily

def UniversalWitnessFamily.toDiagonalFamily
    (U : UniversalWitnessFamily) :
    DiagonalFamily where
  witness := U.witness

def UniversalWitnessFamily.toFailureGenerator
    (U : UniversalWitnessFamily) :
    FailureGenerator (SATBits circuitBitEncoding) :=
  U.toDiagonalFamily.toFailureGenerator

theorem universalWitnessFamily_to_g21
    (U : UniversalWitnessFamily) :
    G21Pointwise := by
  intro M
  exact ⟨(U.witness M).bits,
    diagonal_witness_fails M (U.witness M)⟩

theorem universalWitnessFamilyGap_to_g21
    (h : UniversalWitnessFamilyGap) :
    G21Pointwise := by
  rcases h with ⟨U⟩
  exact universalWitnessFamily_to_g21 U

theorem universalWitnessFamilyGap_to_p02
    (h : UniversalWitnessFamilyGap) :
    P02TerminalFrontier.P02Target :=
  g21_pointwise_iff_p02_target.mp
    (universalWitnessFamilyGap_to_g21 h)

/-- Same-input closure is strong enough to construct the candidate-indexed
semantic witness family. -/
noncomputable def sameInputClosureToUniversalWitnessFamily
    (h : SameInputClosure) :
    UniversalWitnessFamily where
  witness := fun M => sameInputWitnessToDiagonal M (h M)

theorem sameInputClosure_to_universalWitnessFamilyGap
    (h : SameInputClosure) :
    UniversalWitnessFamilyGap :=
  ⟨sameInputClosureToUniversalWitnessFamily h⟩

/- Bare G21 is intentionally not promoted back to UniversalWitnessFamilyGap:
not-CorrectAt may arise from a clock failure and need not contain an explicit
canonical semantic flip witness. -/

#print axioms MCore.Real.P02UniversalWitnessDetailed.universalWitnessFamily_to_g21
#print axioms MCore.Real.P02UniversalWitnessDetailed.universalWitnessFamilyGap_to_p02
#print axioms MCore.Real.P02UniversalWitnessDetailed.sameInputClosure_to_universalWitnessFamilyGap

end P02UniversalWitnessDetailed
end Real
end MCore
