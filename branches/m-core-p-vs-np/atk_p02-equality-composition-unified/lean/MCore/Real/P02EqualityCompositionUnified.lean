import MCore.Real.P02EqualityMaterialAtomsMaterial

namespace MCore
namespace Real
namespace P02EqualityCompositionUnified

open CanonicalFinalProof
open P02EqualityBranchMaterialFrontier
open P02EqualityMaterialAtomsMaterial

/-- Hosted and priority were testing the same mathematical obligation:
given one concrete NP realization and its certified Cook--Levin material,
a deterministic polynomial-time SAT decider lifts to a deterministic
polynomial-time decider for the source language. -/
def HostedCompositionFormula : Prop :=
  ∀ {L : BitLanguage}
    (R : PolyNTMRealization L)
    (C : CookLevinMaterial R),
      InP P02EqualityBranchMaterialFrontier.CanonicalSAT → InP L

def PriorityCompositionFormula : Prop :=
  HostedCompositionFormula

theorem hosted_priority_same_formula :
    HostedCompositionFormula ↔ PriorityCompositionFormula :=
  Iff.rfl

/-- One actual repository composition producer discharges both formerly
separate hosted/priority formulas. -/
def SequentialCompositionUnified
    (comp : DeterministicReductionComposition) :
    HostedCompositionFormula := by
  intro L R C hSAT
  exact comp.lift R C hSAT

theorem unified_implies_priority
    (comp : DeterministicReductionComposition) :
    PriorityCompositionFormula :=
  SequentialCompositionUnified comp

/-- Exact packaging into the already-GREEN equality frontier. -/
def unifiedEqualityProducer
    (cook : UniversalCookLevinMaterializer)
    (comp : DeterministicReductionComposition) :
    EqualityMaterialProducer :=
  { cookLevin := cook
    compose := comp }

theorem unified_satInP_implies_p_eq_np
    (hSAT : InP P02EqualityBranchMaterialFrontier.CanonicalSAT)
    (cook : UniversalCookLevinMaterializer)
    (comp : DeterministicReductionComposition) :
    ∀ L : BitLanguage, InP L ↔ InNP L :=
  equalityMaterialProducer_closes_p_eq_np
    (unifiedEqualityProducer cook comp) hSAT

/-- Honest remaining operational frontier: inhabit the two material atoms.
No reverse implication is asserted. -/
def UNIFIED_COMPOSITION_OPEN_MATH : Prop :=
  Nonempty UniversalCookLevinMaterializer ∧
    Nonempty DeterministicReductionComposition

#print axioms MCore.Real.P02EqualityCompositionUnified.hosted_priority_same_formula
#print axioms MCore.Real.P02EqualityCompositionUnified.SequentialCompositionUnified
#print axioms MCore.Real.P02EqualityCompositionUnified.unified_implies_priority
#print axioms MCore.Real.P02EqualityCompositionUnified.unifiedEqualityProducer
#print axioms MCore.Real.P02EqualityCompositionUnified.unified_satInP_implies_p_eq_np

end P02EqualityCompositionUnified
end Real
end MCore
