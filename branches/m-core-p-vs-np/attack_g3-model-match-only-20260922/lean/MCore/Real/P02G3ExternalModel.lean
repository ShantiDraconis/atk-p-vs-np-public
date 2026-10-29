import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace P02G3ExternalModel

open CanonicalFinalProof
open FailProofAllGaps

/-- G3 is the semantic adapter from the hardened internal machine model to one
externally pinned formalization of P and NP. The external predicates remain
parameters here; this file does not choose them and therefore cannot manufacture
a model match by selecting the internal predicates themselves. -/
def G3Statement
    (officialP officialNP : BitLanguage → Prop) : Prop :=
  Nonempty (ExternalModelMatch officialP officialNP)

/-- Exact closure condition for G3 once the external P/NP predicates have been
pinned by provenance outside this module. -/
def G3ClosureCondition
    (officialP officialNP : BitLanguage → Prop) : Prop :=
  (∀ language, InP language ↔ officialP language) ∧
  (∀ language, InNP language ↔ officialNP language)

theorem g3_statement_iff_closure_condition
    (officialP officialNP : BitLanguage → Prop) :
    G3Statement officialP officialNP ↔
      G3ClosureCondition officialP officialNP := by
  constructor
  · rintro ⟨hMatch⟩
    exact ⟨hMatch.p_match, hMatch.np_match⟩
  · rintro ⟨hP, hNP⟩
    exact ⟨{ p_match := hP, np_match := hNP }⟩

/-- G3 is pure transfer wiring: if the exact model match exists, any internal
separation theorem transfers to the externally pinned predicates. -/
theorem g3_transfers_internal_separation
    {officialP officialNP : BitLanguage → Prop}
    (hG3 : G3Statement officialP officialNP)
    (hInternal : PneqNP) :
    OfficialPneqNP officialP officialNP := by
  rcases hG3 with ⟨hMatch⟩
  exact internal_separation_transfers hMatch hInternal

#print axioms MCore.Real.P02G3ExternalModel.g3_statement_iff_closure_condition
#print axioms MCore.Real.P02G3ExternalModel.g3_transfers_internal_separation

end P02G3ExternalModel
end Real
end MCore
