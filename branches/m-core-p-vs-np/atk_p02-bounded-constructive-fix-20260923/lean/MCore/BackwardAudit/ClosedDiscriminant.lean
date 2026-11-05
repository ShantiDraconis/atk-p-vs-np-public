import MCore.C12.Families

namespace MCore
namespace ClosedDiscriminant

def StartClosed {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∀ L, P L → NP L

def D {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∀ L, NP L → P L

def SeparationWitness {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∃ L, NP L ∧ ¬ P L

def MiddleClosed {Language : Type}
    (P NP : Language → Prop) : Prop :=
  D P NP ∨ SeparationWitness P NP

def EqualityFinal {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∀ L, P L ↔ NP L

def SeparationFinal {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ¬ EqualityFinal P NP

def FinalClosed {Language : Type}
    (P NP : Language → Prop) : Prop :=
  EqualityFinal P NP ∨ SeparationFinal P NP

theorem discriminant_implies_equality
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP) (hD : D P NP) :
    EqualityFinal P NP := by
  intro L
  constructor
  · exact hStart L
  · exact hD L

theorem equality_implies_discriminant
    {Language : Type} {P NP : Language → Prop}
    (hEq : EqualityFinal P NP) :
    D P NP := by
  intro L hNP
  exact (hEq L).mpr hNP

theorem discriminant_iff_equality
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP) :
    D P NP ↔ EqualityFinal P NP := by
  constructor
  · exact discriminant_implies_equality hStart
  · exact equality_implies_discriminant

theorem witness_implies_not_discriminant
    {Language : Type} {P NP : Language → Prop}
    (hW : SeparationWitness P NP) :
    ¬ D P NP := by
  intro hD
  rcases hW with ⟨L, hNP, hNotP⟩
  exact hNotP (hD L hNP)

theorem not_discriminant_implies_witness
    {Language : Type} {P NP : Language → Prop}
    (hNotD : ¬ D P NP) :
    SeparationWitness P NP := by
  exact Classical.byContradiction (fun hNoWitness => by
    apply hNotD
    intro L hNP
    exact Classical.byContradiction (fun hNotP =>
      hNoWitness ⟨L, hNP, hNotP⟩))

theorem not_discriminant_iff_witness
    {Language : Type} (P NP : Language → Prop) :
    (¬ D P NP) ↔ SeparationWitness P NP := by
  constructor
  · exact not_discriminant_implies_witness
  · exact witness_implies_not_discriminant

theorem middle_closed
    {Language : Type} (P NP : Language → Prop) :
    MiddleClosed P NP := by
  rcases Classical.em (D P NP) with hD | hNotD
  · exact Or.inl hD
  · exact Or.inr (not_discriminant_implies_witness hNotD)

theorem middle_exclusive
    {Language : Type} (P NP : Language → Prop) :
    ¬ (D P NP ∧ SeparationWitness P NP) := by
  intro h
  exact witness_implies_not_discriminant h.2 h.1

theorem witness_implies_separation_final
    {Language : Type} {P NP : Language → Prop}
    (hW : SeparationWitness P NP) :
    SeparationFinal P NP := by
  intro hEq
  exact witness_implies_not_discriminant hW (equality_implies_discriminant hEq)

theorem separation_final_implies_not_discriminant
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP)
    (hSep : SeparationFinal P NP) :
    ¬ D P NP := by
  intro hD
  exact hSep (discriminant_implies_equality hStart hD)

theorem separation_final_implies_witness
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP)
    (hSep : SeparationFinal P NP) :
    SeparationWitness P NP :=
  not_discriminant_implies_witness
    (separation_final_implies_not_discriminant hStart hSep)

theorem separation_witness_iff_final
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP) :
    SeparationWitness P NP ↔ SeparationFinal P NP := by
  constructor
  · exact witness_implies_separation_final
  · exact separation_final_implies_witness hStart

theorem final_closed
    {Language : Type} (P NP : Language → Prop) :
    FinalClosed P NP := by
  rcases Classical.em (EqualityFinal P NP) with hEq | hSep
  · exact Or.inl hEq
  · exact Or.inr hSep

theorem middle_to_final
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP)
    (hMiddle : MiddleClosed P NP) :
    FinalClosed P NP := by
  rcases hMiddle with hD | hW
  · exact Or.inl (discriminant_implies_equality hStart hD)
  · exact Or.inr (witness_implies_separation_final hW)

theorem final_to_middle
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP)
    (hFinal : FinalClosed P NP) :
    MiddleClosed P NP := by
  rcases hFinal with hEq | hSep
  · exact Or.inl (equality_implies_discriminant hEq)
  · exact Or.inr (separation_final_implies_witness hStart hSep)

theorem closed_chain
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP) :
    MiddleClosed P NP ∧ FinalClosed P NP := by
  have hMiddle := middle_closed P NP
  exact ⟨hMiddle, middle_to_final hStart hMiddle⟩

theorem bidirectional_convergence
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP) :
    (D P NP ↔ EqualityFinal P NP) ∧
    (SeparationWitness P NP ↔ SeparationFinal P NP) :=
  ⟨discriminant_iff_equality hStart, separation_witness_iff_final hStart⟩

theorem two_sides_false
    {Language : Type} {P NP : Language → Prop} :
    D P NP ∧ SeparationWitness P NP → False := by
  intro h
  exact witness_implies_not_discriminant h.2 h.1

end ClosedDiscriminant
end MCore
