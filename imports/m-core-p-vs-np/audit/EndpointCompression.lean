import MCore.C12.Families

namespace MCore
namespace BackwardCompression

def FINAL_STATEMENT {Language : Type}
    (officialP officialNP : Language → Prop) : Prop :=
  ¬ ∀ L, officialP L ↔ officialNP L

/-- F1: semantic adapter from the repository's abstract class predicates to a
fixed official formalization. No such adapter is assumed globally. -/
structure OfficialModelMatch {Language : Type}
    (C : ClassicalComplexityInterface Language)
    (officialP officialNP : Language → Prop) : Prop where
  p_match : ∀ L, C.inP L ↔ officialP L
  np_match : ∀ L, C.inNP L ↔ officialNP L

/-- Semantic core of a separation witness for one fixed class interface. -/
structure FixedWitness {Language : Type}
    (C : ClassicalComplexityInterface Language) where
  witness : Language
  witness_in_np : C.inNP witness
  witness_not_in_p : ¬ C.inP witness

/-- K10 data, but tied to one fixed classical interface rather than allowing an
existential choice of an arbitrary language universe/model. -/
structure FixedK10WitnessData {Language : Type}
    (C : ClassicalComplexityInterface Language) where
  α : Type
  Value : Type
  data : SeparationWitnessData Language α Value
  classical_eq : data.interface.classical = C

def F1_OfficialModelMatch {Language : Type}
    (C : ClassicalComplexityInterface Language)
    (officialP officialNP : Language → Prop) : Prop :=
  Nonempty (OfficialModelMatch C officialP officialNP)

def F2_FixedK10WitnessExistence {Language : Type}
    (C : ClassicalComplexityInterface Language) : Prop :=
  Nonempty (FixedK10WitnessData C)

/-- C12's strongest natural family-level candidate premise. It is a proposition,
not a theorem and not inferred from the finite CSV. -/
def C12QuantitativeFrontier : Prop :=
  C12.FamilyPayoffObligation 1 1 C12.orN ∧
  C12.FamilyPayoffObligation 1 1 C12.andN ∧
  C12.FamilyPayoffObligation 1 1 C12.reducibleN ∧
  C12.FamilyPayoffObligation 1 1
    (fun n => C12.randomKCNF n (2 * n + 1) 3 0)

/-- OPEN_BRIDGE: the missing mathematical transfer from an asymptotic C12
family statement to witness data for one fixed classical model. -/
def OPEN_BRIDGE {Language : Type}
    (C : ClassicalComplexityInterface Language) : Prop :=
  C12QuantitativeFrontier → F2_FixedK10WitnessExistence C

def k10_data_to_fixed_witness
    {Language α Value : Type}
    (W : SeparationWitnessData Language α Value) :
    FixedWitness W.interface.classical :=
  { witness := W.witness
    witness_in_np := W.witness_in_np
    witness_not_in_p := separation_witness_not_in_P W }

def fixed_k10_to_witness
    {Language : Type}
    {C : ClassicalComplexityInterface Language}
    (W : FixedK10WitnessData C) :
    FixedWitness C := by
  rcases W with ⟨α, Value, data, hclassical⟩
  cases hclassical
  exact k10_data_to_fixed_witness data

/-- Pure logical wiring: once a witness is tied to a fixed model and that model
is matched to the official predicates, the endpoint follows. -/
theorem fixed_witness_implies_final
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

/-- Endpoint compression: all K7-K10 logical plumbing collapses to two real
frontiers for the fixed official model. -/
theorem endpoint_compression
    {Language : Type}
    {C : ClassicalComplexityInterface Language}
    {officialP officialNP : Language → Prop}
    (hF1 : F1_OfficialModelMatch C officialP officialNP)
    (hF2 : F2_FixedK10WitnessExistence C) :
    FINAL_STATEMENT officialP officialNP := by
  rcases hF1 with ⟨hModel⟩
  rcases hF2 with ⟨hK10⟩
  exact fixed_witness_implies_final hModel (fixed_k10_to_witness hK10)

/-- C12 route: F1 + quantitative frontier + OPEN_BRIDGE collapse to FINAL.
The theorem is conditional and does not populate any frontier. -/
theorem endpoint_from_c12_open_bridge
    {Language : Type}
    {C : ClassicalComplexityInterface Language}
    {officialP officialNP : Language → Prop}
    (hF1 : F1_OfficialModelMatch C officialP officialNP)
    (hQuant : C12QuantitativeFrontier)
    (hBridge : OPEN_BRIDGE C) :
    FINAL_STATEMENT officialP officialNP :=
  endpoint_compression hF1 (hBridge hQuant)

end BackwardCompression
end MCore
