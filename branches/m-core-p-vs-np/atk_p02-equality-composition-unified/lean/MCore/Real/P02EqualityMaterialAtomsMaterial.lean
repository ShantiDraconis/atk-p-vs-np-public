import MCore.Real.P02EqualityBranchMaterialFrontier

namespace MCore
namespace Real
namespace P02EqualityMaterialAtomsMaterial

open CanonicalFinalProof
open P02EqualityBranchMaterialFrontier

/-- Atom 1 remains exactly the universal physical Cook--Levin materializer
already isolated by the equality frontier. -/
def COOK_LEVIN_MATERIALIZER_OPEN_MATH : Prop :=
  Nonempty UniversalCookLevinMaterializer

/-- Atom 2 remains exactly deterministic closure under the certified reduction. -/
def DETERMINISTIC_COMPOSITION_OPEN_MATH : Prop :=
  Nonempty DeterministicReductionComposition

/-- Packaging certified inhabitants of both atoms yields the equality producer. -/
def equalityProducerOfAtoms
    (U : UniversalCookLevinMaterializer)
    (C : DeterministicReductionComposition) :
    EqualityMaterialProducer :=
  { cookLevin := U
    compose := C }

/-- With an actual canonical-SAT DTM and both material atoms, equality closes. -/
theorem satInP_plus_atoms_implies_p_eq_np
    (hSAT : InP CanonicalSAT)
    (U : UniversalCookLevinMaterializer)
    (C : DeterministicReductionComposition) :
    ∀ L : BitLanguage, InP L ↔ InNP L :=
  equalityMaterialProducer_closes_p_eq_np
    (equalityProducerOfAtoms U C) hSAT

/-- Honest joint material frontier for the equality branch. -/
def EQUALITY_ATOMS_OPEN_MATH : Prop :=
  Nonempty UniversalCookLevinMaterializer ∧
    Nonempty DeterministicReductionComposition

theorem equalityAtoms_imply_transfer :
    EQUALITY_ATOMS_OPEN_MATH →
      Nonempty P02TwoSidedExactnessAudit.CanonicalSATCompletenessTransfer := by
  rintro ⟨⟨U⟩, ⟨C⟩⟩
  exact ⟨(equalityProducerOfAtoms U C).toTransfer⟩

#print axioms MCore.Real.P02EqualityMaterialAtomsMaterial.equalityProducerOfAtoms
#print axioms MCore.Real.P02EqualityMaterialAtomsMaterial.satInP_plus_atoms_implies_p_eq_np
#print axioms MCore.Real.P02EqualityMaterialAtomsMaterial.equalityAtoms_imply_transfer

end P02EqualityMaterialAtomsMaterial
end Real
end MCore
