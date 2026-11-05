import MCore.Real.P02TableauCompletenessClose
import MCore.Real.P02SemanticFlipCore

namespace MCore
namespace Real
namespace P02CookLevinSameInputCore

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02BoundedComputationEncoding
open P02TableauCompletenessClose
open P02TotalCandidateSemanticCore
open P02SemanticFlipCore

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

/-- Same machine and clock, with the external accepting predicate complemented.
The physical transition system is unchanged. -/
def complementCandidate (M : PolyDTMCandidate) : PolyDTMCandidate where
  stateCount := M.stateCount
  machine := M.machine
  blank_none := M.blank_none
  accepting := fun q => !(M.accepting q)
  timeBound := M.timeBound
  time_poly := M.time_poly

theorem complement_acceptsAtFuel_iff
    (M : PolyDTMCandidate) (x : BitString) (t : Nat) :
    AcceptsAtFuel (complementCandidate M) x t ↔
      ¬ AcceptsAtFuel M x t := by
  unfold AcceptsAtFuel complementCandidate
  simp

/-- Cook-Levin tableau encoding of rejection by M at its declared clock. -/
def rejectCircuit
    (M : PolyDTMCandidate) (x : BitString) : CircuitK1.Circuit :=
  boundedExecCircuit (complementCandidate M) x (M.timeBound x.length)

def rejectTransform
    (M : PolyDTMCandidate) (x : BitString) : BitString :=
  encodeCircuit (rejectCircuit M x)

theorem rejectTransform_valid
    (M : PolyDTMCandidate) (x : BitString) :
    ∃ phi : CircuitK1.Circuit,
      decodeCircuit (rejectTransform M x) = some phi := by
  exact ⟨rejectCircuit M x, decodeCircuit_encode _⟩

/-- Since bounded execution/tableau correctness is now kernel-closed, the
rejection transform has an unconditional semantic specification. -/
theorem rejectTransform_sat_iff_not_accepts
    (M : PolyDTMCandidate) (x : BitString) :
    SATTarget (rejectTransform M x) ↔
      ¬ DeclaredAccepts M x := by
  have hbits :=
    boundedExecCorrectness_to_bits
      boundedExecCorrectness_closed
      (complementCandidate M) x (M.timeBound x.length)
  have hcomp :=
    complement_acceptsAtFuel_iff M x (M.timeBound x.length)
  have h := hbits.trans hcomp
  simpa [rejectTransform, rejectCircuit, boundedExecBits,
    SATTarget, DeclaredAccepts, AcceptsAtFuel] using h

/-- Exact same-input witness needed to turn the Cook-Levin rejection transform
into a semantic diagonal witness.  No existence is asserted here. -/
structure SameInputWitness (M : PolyDTMCandidate) where
  input : BitString
  fixed : input = rejectTransform M input

theorem SameInputWitness.semanticFlip
    {M : PolyDTMCandidate}
    (W : SameInputWitness M) :
    SemanticFlip M W.input := by
  unfold SemanticFlip
  have hProp :
      SATTarget W.input =
        SATTarget (rejectTransform M W.input) :=
    congrArg SATTarget W.fixed
  calc
    SATTarget W.input ↔ SATTarget (rejectTransform M W.input) := by
      constructor
      · exact Eq.mp hProp
      · exact Eq.mpr hProp
    _ ↔ ¬ DeclaredAccepts M W.input :=
      rejectTransform_sat_iff_not_accepts M W.input

/-- The remaining material same-input producer, restricted to candidates that
halt within their own declared clocks. -/
def TotalCandidateSameInputCore : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
      Nonempty (SameInputWitness M)

theorem sameInputCore_implies_semanticFlipCore
    (H : TotalCandidateSameInputCore) :
    TotalCandidateSemanticFlipCore := by
  intro M hTotal
  rcases H M hTotal with ⟨W⟩
  exact ⟨W.input, W.semanticFlip⟩

theorem sameInputCore_implies_universal_failure
    (H : TotalCandidateSameInputCore) :
    UniversalFailure SATTarget :=
  (semantic_flip_core_iff_universal_failure).mp
    (sameInputCore_implies_semanticFlipCore H)

theorem sameInputCore_closes_internal_endpoint
    (H : TotalCandidateSameInputCore) :
    PneqNP :=
  semantic_flip_core_closes_internal_endpoint
    (sameInputCore_implies_semanticFlipCore H)

#print axioms MCore.Real.P02CookLevinSameInputCore.complement_acceptsAtFuel_iff
#print axioms MCore.Real.P02CookLevinSameInputCore.rejectTransform_valid
#print axioms MCore.Real.P02CookLevinSameInputCore.rejectTransform_sat_iff_not_accepts
#print axioms MCore.Real.P02CookLevinSameInputCore.SameInputWitness.semanticFlip
#print axioms MCore.Real.P02CookLevinSameInputCore.sameInputCore_implies_semanticFlipCore
#print axioms MCore.Real.P02CookLevinSameInputCore.sameInputCore_implies_universal_failure

end P02CookLevinSameInputCore
end Real
end MCore
