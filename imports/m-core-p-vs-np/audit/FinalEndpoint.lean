import MCore.K9

namespace MCore
namespace BackwardAudit

/-- Equality-side final statement, definition only. -/
def EQUALITY_FINAL_STATEMENT {Language : Type}
    (officialP officialNP : Language → Prop) : Prop :=
  ∀ L, officialP L ↔ officialNP L

/-- Separation-side final statement, definition only. -/
def SEPARATION_FINAL_STATEMENT {Language : Type}
    (officialP officialNP : Language → Prop) : Prop :=
  ¬ EQUALITY_FINAL_STATEMENT officialP officialNP

/-- Historical endpoint name retained for compatibility with the existing
backward-dense separation route. -/
def FINAL_STATEMENT {Language : Type}
    (officialP officialNP : Language → Prop) : Prop :=
  SEPARATION_FINAL_STATEMENT officialP officialNP

/-- The same separation endpoint shape specialized to the repository's abstract
interface. It remains abstract until a concrete official-model match exists. -/
def FINAL_STATEMENT_for_interface {Language : Type}
    (C : ClassicalComplexityInterface Language) : Prop :=
  FINAL_STATEMENT C.inP C.inNP

theorem equality_final_unfold {Language : Type}
    (officialP officialNP : Language → Prop) :
    EQUALITY_FINAL_STATEMENT officialP officialNP ↔
      ∀ L, officialP L ↔ officialNP L := Iff.rfl

theorem separation_final_unfold {Language : Type}
    (officialP officialNP : Language → Prop) :
    SEPARATION_FINAL_STATEMENT officialP officialNP ↔
      ¬ ∀ L, officialP L ↔ officialNP L := Iff.rfl

theorem final_statement_unfold {Language : Type}
    (officialP officialNP : Language → Prop) :
    FINAL_STATEMENT officialP officialNP ↔
      ¬ ∀ L, officialP L ↔ officialNP L := Iff.rfl

/-- Audit metadata only: these propositions/results are forbidden as hidden
premises in any attempted endpoint proof. -/
def forbiddenHypotheses : List String :=
  [ "EQUALITY_FINAL_STATEMENT itself"
  , "SEPARATION_FINAL_STATEMENT itself"
  , "NP subset P without a proof"
  , "existence of an NP language outside P without a proof"
  , "PApproxNPResearchZone treated as a third classical outcome"
  , "existence of K10 witness data for arbitrary types treated as the official model"
  , "C12 finite PaysOff measurements treated as an asymptotic theorem"
  , "an unproved quantitative-to-classical transfer bridge"
  ]

end BackwardAudit
end MCore
