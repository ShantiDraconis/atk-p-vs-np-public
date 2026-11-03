import MCore.Real.P02BoundedComputationClose
import MCore.Real.P02KleeneKernel

namespace MCore
namespace Real
namespace P02RecoveredTableauKernel

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02BoundedComputationEncoding
open P02BoundedComputationClose
open P02KleeneKernel

/-- Transition soundness is already constructed in the recovered T5-A1 source.
Only tableau completeness remains as an input to full bounded-execution correctness. -/
theorem boundedExecCorrectness_of_tableauCompleteness
    (C : TableauCompletenessCertificate) :
    BoundedExecCorrectness :=
  certificates_close_boundedExecCorrectness
    transitionSoundnessCertificate C

def TableauCompletenessOnlyGap : Prop :=
  Nonempty TableauCompletenessCertificate

theorem tableauCompletenessOnly_closes_boundedExec
    (h : TableauCompletenessOnlyGap) :
    BoundedExecCorrectness := by
  rcases h with ⟨C⟩
  exact boundedExecCorrectness_of_tableauCompleteness C

/-- Canonical SAT encoding of the candidate's run at exactly its declared clock. -/
def declaredExecutionBits
    (M : PolyDTMCandidate)
    (x : BitString) : BitString :=
  boundedExecBits M x (M.timeBound x.length)

/-- Once tableau completeness is supplied, the recovered tableau encoding
represents the candidate's declared acceptance bit exactly. -/
theorem declaredExecutionBits_sat_iff_declaredAccept
    (hBounded : BoundedExecCorrectness)
    (M : PolyDTMCandidate)
    (x : BitString) :
    SATTarget (declaredExecutionBits M x) ↔
      DeclaredAccept M x := by
  simpa [declaredExecutionBits, SATTarget, DeclaredAccept, AcceptsAtFuel] using
    (boundedExecCorrectness_to_bits hBounded M x (M.timeBound x.length))

/-- Combined form using only the remaining tableau-completeness certificate. -/
theorem declaredExecutionBits_sat_iff_of_tableauCompleteness
    (C : TableauCompletenessCertificate)
    (M : PolyDTMCandidate)
    (x : BitString) :
    SATTarget (declaredExecutionBits M x) ↔
      DeclaredAccept M x :=
  declaredExecutionBits_sat_iff_declaredAccept
    (boundedExecCorrectness_of_tableauCompleteness C) M x

end P02RecoveredTableauKernel
end Real
end MCore
