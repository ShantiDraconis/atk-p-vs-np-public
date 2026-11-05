namespace Audit.OfficialModel

structure LowerBoundWitness where
  L : OfficialLanguage
  L_in_NP : OfficialNP L
  L_not_in_P : ¬ OfficialP L

def F2_FixedWitnessExistence : Prop :=
  Nonempty LowerBoundWitness

theorem lower_bound_witness_separates (W : LowerBoundWitness) :
    ¬ (∀ L : OfficialLanguage, OfficialP L ↔ OfficialNP L) := by
  intro hEq
  exact W.L_not_in_P ((hEq W.L).mpr W.L_in_NP)

theorem F2_implies_separation :
    F2_FixedWitnessExistence →
      ¬ (∀ L : OfficialLanguage, OfficialP L ↔ OfficialNP L) := by
  rintro ⟨W⟩
  exact lower_bound_witness_separates W

def F2TypeStatus : String := "PROVED_INTERNAL_FIXED_UNIVERSE"
def F2ExistenceStatus : String := "OPEN_MATHEMATICS"
def F2ExactResidue : String := "EXISTS_L_IN_OFFICIAL_NP_WITH_L_NOT_IN_OFFICIAL_P"

#print axioms Audit.OfficialModel.lower_bound_witness_separates
#print axioms Audit.OfficialModel.F2_implies_separation

end Audit.OfficialModel
