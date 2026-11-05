import MCore.Real.P02EqualityBranchMaterialFrontier

namespace MCore
namespace Real
namespace P02DeterministicCompositionAtom

open CanonicalFinalProof
open P02EqualityBranchMaterialFrontier

/-- Exact operational obligation for atom 2. -/
def DETERMINISTIC_COMPOSITION_OPEN_MATH : Prop :=
  Nonempty DeterministicReductionComposition

/-- Pointwise composition law from a certified Cook--Levin reduction and one
canonical SAT DTM to a DTM for the source NP language. -/
def PointwiseCompositionLaw : Prop :=
  ∀ {L : BitLanguage}
    (R : PolyNTMRealization L)
    (C : CookLevinMaterial R)
    (S : PolyDTMRealization CanonicalSAT),
      Nonempty (PolyDTMRealization L)

/-- Packaging the pointwise law yields the repository's atom-2 producer. -/
noncomputable def composition_of_pointwise
    (H : PointwiseCompositionLaw) :
    DeterministicReductionComposition := by
  classical
  refine { lift := ?_ }
  intro L R C hSAT
  rcases hSAT with ⟨S⟩
  exact H R C S

/-- Conversely, atom 2 gives the pointwise law. -/
theorem composition_implies_pointwise
    (C : DeterministicReductionComposition) :
    PointwiseCompositionLaw := by
  intro L R M S
  exact C.lift R M ⟨S⟩

theorem composition_iff_pointwise :
    Nonempty DeterministicReductionComposition ↔
      PointwiseCompositionLaw := by
  constructor
  · rintro ⟨C⟩
    exact composition_implies_pointwise C
  · intro H
    exact ⟨composition_of_pointwise H⟩

#print axioms MCore.Real.P02DeterministicCompositionAtom.composition_of_pointwise
#print axioms MCore.Real.P02DeterministicCompositionAtom.composition_implies_pointwise
#print axioms MCore.Real.P02DeterministicCompositionAtom.composition_iff_pointwise

end P02DeterministicCompositionAtom
end Real
end MCore
