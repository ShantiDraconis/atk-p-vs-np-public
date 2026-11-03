import Mathlib
import MCore.Real.OpenMathCore.Behavior
import MCore.Real.P02UniversalFailureAlgebra

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open P02UniversalFailureAlgebra
open P02G21G22Attack

def T5FCore : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
      ∃ x : BitString, SemanticMismatch M x

theorem separationLaw_implies_T5FCore
    (L : TotalCandidateSeparationLaw) : T5FCore :=
  totalCandidateSeparationLaw_closes_core L

theorem T5FCore_implies_totalityOrSemantic
    (h : T5FCore) :
    TotalityOrSemanticCounterexample := by
  intro M
  by_cases hTotal : DeclaredClockTotal M
  · exact Or.inr (h M hTotal)
  · exact Or.inl hTotal

theorem T5FCore_implies_G21
    (h : T5FCore) :
    G21Pointwise := by
  exact g21_iff_totality_or_semantic_counterexample.mpr
    (T5FCore_implies_totalityOrSemantic h)

theorem T5FCore_implies_P02
    (h : T5FCore) :
    P02TerminalFrontier.P02Target := by
  exact totality_or_semantic_closes_p02
    (T5FCore_implies_totalityOrSemantic h)

/-- Fail-closed: all arithmetic/algebra/topology/calculus infrastructure is
auxiliary until an actual separation law is constructed. -/
def OpenMathTerminalGap : Prop :=
  Nonempty TotalCandidateSeparationLaw

theorem openMathTerminalGap_implies_T5FCore
    (h : OpenMathTerminalGap) : T5FCore := by
  rcases h with ⟨L⟩
  exact separationLaw_implies_T5FCore L

#print axioms MCore.Real.OpenMathCore.T5FCore_implies_G21
#print axioms MCore.Real.OpenMathCore.T5FCore_implies_P02
#print axioms MCore.Real.OpenMathCore.openMathTerminalGap_implies_T5FCore

end MCore.Real.OpenMathCore
