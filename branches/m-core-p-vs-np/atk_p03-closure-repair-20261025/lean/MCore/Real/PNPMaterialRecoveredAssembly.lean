import MCore.Real.PNPMaterialLowerBoundFrontier
import MCore.Real.P02ExactDiagonalFrontier
import MCore.Real.P02SameInputProducer
import MCore.Real.P02TotalCandidateKleeneReduction
import MCore.Real.P02ComplementRunRealization
import MCore.Real.P02BehavioralAlignment

namespace MCore
namespace Real
namespace PNPMaterialRecoveredAssembly

open CanonicalFinalProof
open PNPPromotedByMaterial
open PNPMaterialLowerBoundFrontier
open P02UniversalFailureMinCut
open P02ExactDiagonalFrontier
open P02SameInputProducer
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization

/--
Recovered semantic core after all already-closed physical machinery is removed.

For candidates that halt within their declared clock on every input, produce
one same-input semantic flip. Non-total candidates are handled separately by
the already-proved timeout branch.
-/
def RecoveredTotalSemanticCore : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
      ∃ x : BitString,
        P02UniversalFailureMinCut.CanonicalSAT x ↔
          ¬ P02KleeneUniversalBridge.DeclaredAccepts M x

/-- The recovered total-candidate semantic core gives the exact diagonal
producer used by the existing timeout/semantic split. -/
theorem recoveredCore_to_exactDiagonal
    (H : RecoveredTotalSemanticCore) :
    TotalExactDiagonalProducer := by
  intro M hTotal
  exact H M hTotal

/-- Assemble a concrete candidate-indexed lower-bound producer.  This theorem
uses no PneqNP, not-InP, UniversalFailure, or lower-bound hypothesis. -/
noncomputable def recoveredCore_to_lowerBoundProducer
    (H : RecoveredTotalSemanticCore) :
    CanonicalSATLowerBoundProducer := by
  let B : TotalExactDiagonalProducer := recoveredCore_to_exactDiagonal H
  let UF : UniversalFailure P02UniversalFailureMinCut.CanonicalSAT :=
    total_exact_diagonal_implies_universal_failure B
  refine
    { counterexample := fun M => Classical.choose (UF M)
      fails := ?_ }
  intro M
  exact Classical.choose_spec (UF M)

/-- Direct material promotion from the recovered semantic core. -/
noncomputable def recoveredCore_to_promotedMaterial
    (H : RecoveredTotalSemanticCore) :
    PromotedByMaterialPNP :=
  { lowerBound := recoveredCore_to_lowerBoundProducer H }

/-- The reconstructed proof chain closes the internal endpoint once the exact
same-input semantic core is supplied. -/
theorem recoveredCore_closes_PneqNP
    (H : RecoveredTotalSemanticCore) :
    PneqNP := by
  exact promoted_material_PneqNP (recoveredCore_to_promotedMaterial H)

/-- Existing same-input diagonal data is sufficient for the recovered core. -/
theorem sameInputProducer_to_recoveredCore
    (P : SameInputSemanticDiagonalProducer) :
    RecoveredTotalSemanticCore := by
  intro M _hTotal
  exact ⟨P.diagonalInput M, P.flip M⟩

/-- Existing total-candidate Kleene bridges are also sufficient. -/
theorem totalKleene_to_lowerBoundProducer
    (B : TotalCandidateKleeneBridge) :
    CanonicalSATLowerBoundProducer := by
  let U : UniversalCounterexampleProducer := producerOfTotalKleene B
  exact fromUniversalCounterexampleProducer U

/-- The concrete complemented bounded-run Cook--Levin reduction is already
available for every total-clock candidate.  It yields a semantic flip as soon
as the source and generated SAT instance are behaviorally aligned. -/
theorem complementReduction_recovered_fragment
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (hAlign :
      P02BehavioralAlignment.BehavioralSelfAlignment M hTotal) :
    ExactDiagonalWitness M := by
  exact P02BehavioralAlignment.behavioral_alignment_gives_exact_witness
    M hTotal hAlign

/--
Exact remaining recovered gap.

Everything below this point is already kernel-proved in the current repository:
timeout failure, deterministic complement realization, bounded tableau/Cook--Levin
reduction, and transport from an exact semantic flip to candidate failure.

What remains is the uniform same-input semantic alignment for total candidates.
-/
abbrev RecoveredMaterialGap : Prop := RecoveredTotalSemanticCore

theorem recoveredMaterialGap_closes_materialPromotion
    (h : RecoveredMaterialGap) :
    MaterialPromotionTarget := by
  exact ⟨recoveredCore_to_promotedMaterial h⟩

#print axioms MCore.Real.PNPMaterialRecoveredAssembly.recoveredCore_to_exactDiagonal
#print axioms MCore.Real.PNPMaterialRecoveredAssembly.recoveredCore_to_lowerBoundProducer
#print axioms MCore.Real.PNPMaterialRecoveredAssembly.recoveredCore_closes_PneqNP
#print axioms MCore.Real.PNPMaterialRecoveredAssembly.sameInputProducer_to_recoveredCore
#print axioms MCore.Real.PNPMaterialRecoveredAssembly.totalKleene_to_lowerBoundProducer
#print axioms MCore.Real.PNPMaterialRecoveredAssembly.complementReduction_recovered_fragment
#print axioms MCore.Real.PNPMaterialRecoveredAssembly.recoveredMaterialGap_closes_materialPromotion

end PNPMaterialRecoveredAssembly
end Real
end MCore
