import MCore.C12.Families

namespace MCore
namespace ThreeTracks

/-- Classical wiring already known externally for the official classes:
P is contained in NP. Inside the audit this is always supplied explicitly. -/
def PSubsetNP {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∀ L, P L → NP L

/-- E0: equality-track start.
With P ⊆ NP already supplied, this is exactly the missing reverse inclusion. -/
def E0 {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∀ L, NP L → P L

/-- EF: equality-track final boundary. -/
def EF {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∀ L, P L ↔ NP L

/-- S0: separation-track start; an explicit NP language outside P. -/
def S0 {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∃ L, NP L ∧ ¬ P L

/-- SF: separation-track final boundary. -/
def SF {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ¬ EF P NP

/-- Quantitative C12 frontier reused as the audit meaning of the intermediate
"approximately P/NP" research zone. This is NOT a third classical relation
between P and NP, and finite C12 data do not prove it. -/
def QuantitativeCore : Prop :=
  C12.FamilyPayoffObligation 1 1 C12.orN ∧
  C12.FamilyPayoffObligation 1 1 C12.andN ∧
  C12.FamilyPayoffObligation 1 1 C12.reducibleN ∧
  C12.FamilyPayoffObligation 1 1
    (fun n => C12.randomKCNF n (2 * n + 1) 3 0)

/-- A0: beginning of the quantitative intermediate zone. -/
def A0 : Prop := QuantitativeCore

/-- Human-facing alias for the research notation P≈NP.
It deliberately has no status as a classical complexity-theory relation. -/
def PApproxNPResearchZone : Prop := A0

/-- AF: end of the intermediate zone.
To leave the zone one must deliver either the equality-track start E0 or the
separation-track start S0 for the already-fixed class predicates. -/
def AF {Language : Type}
    (P NP : Language → Prop) : Prop :=
  E0 P NP ∨ S0 P NP

/-- The genuine open middle bridge. No theorem in this file inhabits it. -/
def ApproximationBridge {Language : Type}
    (P NP : Language → Prop) : Prop :=
  A0 → AF P NP

theorem e0_unfold {Language : Type} (P NP : Language → Prop) :
    E0 P NP ↔ ∀ L, NP L → P L := Iff.rfl

theorem ef_unfold {Language : Type} (P NP : Language → Prop) :
    EF P NP ↔ ∀ L, P L ↔ NP L := Iff.rfl

theorem s0_unfold {Language : Type} (P NP : Language → Prop) :
    S0 P NP ↔ ∃ L, NP L ∧ ¬ P L := Iff.rfl

theorem sf_unfold {Language : Type} (P NP : Language → Prop) :
    SF P NP ↔ ¬ EF P NP := Iff.rfl

theorem a0_unfold :
    A0 ↔ QuantitativeCore := Iff.rfl

theorem af_unfold {Language : Type} (P NP : Language → Prop) :
    AF P NP ↔ E0 P NP ∨ S0 P NP := Iff.rfl

/-- Equality track: once the reverse inclusion is proved, P ⊆ NP supplies the
other direction and the final equality boundary follows. -/
theorem equality_start_to_final
    {Language : Type}
    {P NP : Language → Prop}
    (hSub : PSubsetNP P NP)
    (hE0 : E0 P NP) :
    EF P NP := by
  intro L
  constructor
  · exact hSub L
  · exact hE0 L

/-- Equality final boundary trivially recovers the equality start. -/
theorem equality_final_to_start
    {Language : Type}
    {P NP : Language → Prop}
    (hEF : EF P NP) :
    E0 P NP := by
  intro L hNP
  exact (hEF L).mpr hNP

theorem equality_start_final_equiv
    {Language : Type}
    {P NP : Language → Prop}
    (hSub : PSubsetNP P NP) :
    E0 P NP ↔ EF P NP := by
  constructor
  · exact equality_start_to_final hSub
  · exact equality_final_to_start

/-- Separation track: one explicit NP \ P witness is enough to refute equality. -/
theorem separation_start_to_final
    {Language : Type}
    {P NP : Language → Prop}
    (hS0 : S0 P NP) :
    SF P NP := by
  intro hEq
  rcases hS0 with ⟨L, hNP, hNotP⟩
  exact hNotP ((hEq L).mpr hNP)

/-- Under the already-known inclusion P ⊆ NP, a failure of extensional equality
classically yields an NP \ P witness. -/
theorem separation_final_to_start
    {Language : Type}
    {P NP : Language → Prop}
    (hSub : PSubsetNP P NP)
    (hSF : SF P NP) :
    S0 P NP := by
  exact Classical.byContradiction (fun hNoWitness => by
    apply hSF
    intro L
    constructor
    · exact hSub L
    · intro hNP
      exact Classical.byContradiction (fun hNotP =>
        hNoWitness ⟨L, hNP, hNotP⟩))

theorem separation_start_final_equiv
    {Language : Type}
    {P NP : Language → Prop}
    (hSub : PSubsetNP P NP) :
    S0 P NP ↔ SF P NP := by
  constructor
  · exact separation_start_to_final
  · exact separation_final_to_start hSub

/-- AF is not a third endpoint. Once AF is supplied, it resolves into one of
the two classical final boundaries. -/
theorem approximation_end_to_classical_final
    {Language : Type}
    {P NP : Language → Prop}
    (hSub : PSubsetNP P NP)
    (hAF : AF P NP) :
    EF P NP ∨ SF P NP := by
  rcases hAF with hE0 | hS0
  · exact Or.inl (equality_start_to_final hSub hE0)
  · exact Or.inr (separation_start_to_final hS0)

/-- Full conditional middle route. The only non-wiring input here is an actual
ApproximationBridge. -/
theorem approximation_route
    {Language : Type}
    {P NP : Language → Prop}
    (hSub : PSubsetNP P NP)
    (hA0 : A0)
    (hBridge : ApproximationBridge P NP) :
    EF P NP ∨ SF P NP :=
  approximation_end_to_classical_final hSub (hBridge hA0)

/-- The two final classical boundaries are definitionally complementary. -/
theorem separation_final_is_not_equality
    {Language : Type}
    (P NP : Language → Prop) :
    SF P NP ↔ ¬ EF P NP := Iff.rfl

#print axioms equality_start_to_final
#print axioms separation_start_to_final
#print axioms approximation_end_to_classical_final
#print axioms approximation_route

end ThreeTracks
end MCore
