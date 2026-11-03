import MCore.Real.P02RejectionImageOrbit
import MCore.Real.P02FiniteCandidateDescription

namespace MCore
namespace Real
namespace P02DiagonalNoShortcut

open CanonicalFinalProof
open P02SemanticSelfSubstitution
open P02RejectionImageEscape
open P02RejectionImageOrbit
open P02FiniteCandidateDescription

/-- Merely possessing a finite code for M does not supply the semantic
fixed-point required by RejectImageEscape.  This is the exact additional
property that a genuine self-reference construction would have to prove. -/
def CandidateCodeSemanticFixedPoint : Prop :=
  ∀ M : PolyDTMCandidate,
    (∀ y : BitString, OwnClockHalts M y) →
      observedBit M (rejectCode M (candidateCode M)) =
        observedBit M (candidateCode M)

/-- If the candidate code itself satisfied the missing semantic fixed-point
law, the active OPEN_MATH would close immediately. -/
theorem candidateCodeSemanticFixedPoint_implies_escape
    (H : CandidateCodeSemanticFixedPoint) :
    RejectImageEscape := by
  apply rejectImageEscape_iff_totalClockAntiAlternation.mpr
  intro M hTotal hFlip
  have hfixed := H M hTotal
  have hflipped := hFlip (candidateCode M)
  cases hsrc : observedBit M (candidateCode M) <;>
    cases hdst : observedBit M (rejectCode M (candidateCode M)) <;>
    simp_all

/-- The code layer alone is intentionally not promoted to a fixed-point
theorem. The remaining content is exactly the semantic law above. -/
theorem candidateCode_fixedPoint_is_sufficient :
    CandidateCodeSemanticFixedPoint →
      RejectImageOddSemanticRecurrence := by
  intro H M hTotal
  exact ⟨candidateCode M, H M hTotal⟩

#print axioms MCore.Real.P02DiagonalNoShortcut.candidateCodeSemanticFixedPoint_implies_escape
#print axioms MCore.Real.P02DiagonalNoShortcut.candidateCode_fixedPoint_is_sufficient

end P02DiagonalNoShortcut
end Real
end MCore
