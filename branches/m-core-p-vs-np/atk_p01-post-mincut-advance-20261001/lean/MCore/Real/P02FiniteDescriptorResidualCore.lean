import MCore.Real.P02FiniteDescriptorReduction
import MCore.Real.P02SemanticTransformerDichotomy

namespace MCore
namespace Real
namespace P02FiniteDescriptorResidualCore

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02FailureNormalForms
open P02TotalCandidateSemanticCore
open P02FiniteDescriptorReduction
open P02SemanticTransformerCore
open P02SemanticTransformerDichotomy

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

def DescriptorTotal
    (D : FiniteDTMDescriptor) : Prop :=
  DeclaredClockTotal D.toCandidate

def DescriptorConstantCorrect
    (D : FiniteDTMDescriptor) : Prop :=
  ConstantCorrectPattern D.toCandidate

/-- Exact finite-descriptor residual after eliminating clock failures and the
two constant SAT mistakes. -/
def FiniteDescriptorResidual : Prop :=
  ∀ D : FiniteDTMDescriptor,
    DescriptorTotal D →
    DescriptorConstantCorrect D →
      ∃ x : BitString,
        SemanticDisagreement D.toCandidate x

theorem failure_of_not_total
    (D : FiniteDTMDescriptor)
    (hNotTotal : ¬ DescriptorTotal D) :
    ∃ x : BitString,
      ¬ D.toCandidate.CorrectAt SATTarget x := by
  rcases exists_timeout_of_not_total D.toCandidate hNotTotal with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  intro hCorrect
  exact hx hCorrect.1

theorem failure_of_not_constant_correct
    (D : FiniteDTMDescriptor)
    (hTotal : DescriptorTotal D)
    (hNotPattern : ¬ DescriptorConstantCorrect D) :
    ∃ x : BitString,
      ¬ D.toCandidate.CorrectAt SATTarget x := by
  rcases alignment_of_not_constantCorrectPattern
      D.toCandidate hNotPattern with ⟨seed, hAlign⟩
  let y := semanticNegationBits D.toCandidate seed
  refine ⟨y, ?_⟩
  intro hCorrect
  have hBad :
      ¬ (D.toCandidate.accepting
          (D.toCandidate.machine.run
            (D.toCandidate.timeBound y.length)
            (initialTMConfig D.toCandidate.machine y)).state = true ↔
        SATTarget y) := by
    simpa [y] using
      transformed_output_fails_semantically D.toCandidate seed hAlign
  exact hBad hCorrect.2

theorem residual_implies_finiteDescriptorFailure
    (H : FiniteDescriptorResidual) :
    FiniteDescriptorFailure := by
  intro D
  classical
  by_cases hTotal : DescriptorTotal D
  · by_cases hPattern : DescriptorConstantCorrect D
    · rcases H D hTotal hPattern with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      intro hCorrect
      have hBad :
          ¬ (D.toCandidate.accepting
              (D.toCandidate.machine.run
                (D.toCandidate.timeBound x.length)
                (initialTMConfig D.toCandidate.machine x)).state = true ↔
            SATTarget x) :=
        (semanticDisagreement_iff_not_semantic_correct
          D.toCandidate x).mp hx
      exact hBad hCorrect.2
    · exact failure_of_not_constant_correct D hTotal hPattern
  · exact failure_of_not_total D hTotal

theorem finiteDescriptorFailure_implies_residual
    (H : FiniteDescriptorFailure) :
    FiniteDescriptorResidual := by
  intro D hTotal hPattern
  rcases H D with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hHalt : DeclaredHalts D.toCandidate x := hTotal x
  apply (semanticDisagreement_iff_not_semantic_correct
      D.toCandidate x).mpr
  intro hSem
  exact hx ⟨hHalt, hSem⟩

theorem residual_iff_finiteDescriptorFailure :
    FiniteDescriptorResidual ↔ FiniteDescriptorFailure := by
  constructor
  · exact residual_implies_finiteDescriptorFailure
  · exact finiteDescriptorFailure_implies_residual

theorem residual_iff_universalFailure :
    FiniteDescriptorResidual ↔ UniversalFailure SATTarget := by
  exact residual_iff_finiteDescriptorFailure.trans
    finiteDescriptorFailure_iff_universalFailure

theorem residual_closes_internal_endpoint
    (H : FiniteDescriptorResidual) :
    PneqNP :=
  finiteDescriptorFailure_closes_internal_endpoint
    (residual_implies_finiteDescriptorFailure H)

#print axioms MCore.Real.P02FiniteDescriptorResidualCore.failure_of_not_total
#print axioms MCore.Real.P02FiniteDescriptorResidualCore.failure_of_not_constant_correct
#print axioms MCore.Real.P02FiniteDescriptorResidualCore.residual_iff_finiteDescriptorFailure
#print axioms MCore.Real.P02FiniteDescriptorResidualCore.residual_iff_universalFailure
#print axioms MCore.Real.P02FiniteDescriptorResidualCore.residual_closes_internal_endpoint

end P02FiniteDescriptorResidualCore
end Real
end MCore
