import MCore.BackwardAudit.ClosedDiscriminant

namespace MCore
namespace ClosedDiscriminant

theorem test_equality_final_to_middle
    {Language : Type} {P NP : Language → Prop}
    (hEq : EqualityFinal P NP) :
    D P NP :=
  equality_implies_discriminant hEq

theorem test_separation_final_to_middle
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP)
    (hSep : SeparationFinal P NP) :
    SeparationWitness P NP :=
  separation_final_implies_witness hStart hSep

theorem test_final_envelope_to_middle
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP)
    (hFinal : FinalClosed P NP) :
    MiddleClosed P NP :=
  final_to_middle hStart hFinal

theorem test_bidirectional_same_discriminant
    {Language : Type} {P NP : Language → Prop}
    (hStart : StartClosed P NP) :
    (D P NP ↔ EqualityFinal P NP) ∧
    (SeparationWitness P NP ↔ SeparationFinal P NP) :=
  bidirectional_convergence hStart

theorem test_inconsistency_detector
    {Language : Type} {P NP : Language → Prop}
    (hD : D P NP)
    (hW : SeparationWitness P NP) :
    False :=
  two_sides_false ⟨hD, hW⟩

#print axioms test_equality_final_to_middle
#print axioms test_separation_final_to_middle
#print axioms test_final_envelope_to_middle
#print axioms test_bidirectional_same_discriminant
#print axioms test_inconsistency_detector

end ClosedDiscriminant
end MCore
