import MCore.C12.Families

namespace MCore
namespace BackwardRepro

def FINAL_STATEMENT {Language : Type}
    (officialP officialNP : Language → Prop) : Prop :=
  ¬ ∀ L, officialP L ↔ officialNP L

structure OfficialModelMatch {Language : Type}
    (C : ClassicalComplexityInterface Language)
    (officialP officialNP : Language → Prop) : Prop where
  p_match : ∀ L, C.inP L ↔ officialP L
  np_match : ∀ L, C.inNP L ↔ officialNP L

structure FixedWitness {Language : Type}
    (C : ClassicalComplexityInterface Language) where
  witness : Language
  witness_in_np : C.inNP witness
  witness_not_in_p : ¬ C.inP witness

theorem endpoint_from_fixed_witness
    {Language : Type}
    {C : ClassicalComplexityInterface Language}
    {officialP officialNP : Language → Prop}
    (hModel : OfficialModelMatch C officialP officialNP)
    (W : FixedWitness C) :
    FINAL_STATEMENT officialP officialNP := by
  intro hEq
  have hOfficialNP : officialNP W.witness :=
    (hModel.np_match W.witness).mp W.witness_in_np
  have hOfficialP : officialP W.witness :=
    (hEq W.witness).mpr hOfficialNP
  have hAbstractP : C.inP W.witness :=
    (hModel.p_match W.witness).mpr hOfficialP
  exact W.witness_not_in_p hAbstractP

/-- Dense reproduction of the already-proved K10 conditional logic into the
fixed-witness semantic core. This does not prove witness existence. -/
def k10_reproduces_fixed_witness
    {Language α Value : Type}
    (W : SeparationWitnessData Language α Value) :
    FixedWitness W.interface.classical :=
  { witness := W.witness
    witness_in_np := W.witness_in_np
    witness_not_in_p := separation_witness_not_in_P W }

#check C10.VarsNonincreaseObligation
#check C10.ProgressCoverageObligation
#check C11.UniversalPayoffObligation
#check C12.FamilyPayoffObligation
#check k10_open_obligation

#print axioms witness_separates_classes
#print axioms separation_witness_separates
#print axioms endpoint_from_fixed_witness
#print axioms k10_reproduces_fixed_witness
#print axioms C12.c12_classical_endpoint_not_promoted

end BackwardRepro
end MCore
