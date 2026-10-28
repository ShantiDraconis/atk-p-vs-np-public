import MCore.BackwardAudit.ClosedDiscriminant

namespace MCore
namespace BackwardAudit

open ClosedDiscriminant

structure PolySATCertificate
    (SATInstance : Type)
    (SAT : SATInstance → Prop) where
  decide : SATInstance → Bool
  size : SATInstance → Nat
  runtime : SATInstance → Nat
  exponent : Nat
  coefficient : Nat
  correct : ∀ x, decide x = true ↔ SAT x
  runtime_poly :
    ∀ x, runtime x ≤ coefficient * (size x + 1) ^ exponent

structure SATCompletenessTransfer
    {Language SATInstance : Type}
    (P NP : Language → Prop)
    (SAT : SATInstance → Prop) where
  to_discriminant :
    PolySATCertificate SATInstance SAT → D P NP

theorem typeA_closes_equality
    {Language SATInstance : Type}
    {P NP : Language → Prop}
    {SAT : SATInstance → Prop}
    (hStart : StartClosed P NP)
    (alg : PolySATCertificate SATInstance SAT)
    (transfer : SATCompletenessTransfer P NP SAT) :
    EqualityFinal P NP :=
  discriminant_implies_equality hStart (transfer.to_discriminant alg)

structure LowerBoundWitness
    {Language : Type}
    (P NP : Language → Prop) where
  language : Language
  in_np : NP language
  not_in_p : ¬ P language

def LowerBoundWitness.toSeparationWitness
    {Language : Type}
    {P NP : Language → Prop}
    (w : LowerBoundWitness P NP) :
    SeparationWitness P NP :=
  ⟨w.language, w.in_np, w.not_in_p⟩

theorem typeB_closes_separation
    {Language : Type}
    {P NP : Language → Prop}
    (w : LowerBoundWitness P NP) :
    SeparationFinal P NP :=
  witness_implies_separation_final w.toSeparationWitness

inductive BarrierStatus
  | notAssessed
  | evidenceOfEscape
  | appearsToRelativize
  | appearsNatural
  | appearsToAlgebrize
  deriving Repr, DecidableEq

structure SeparationTechniqueAudit where
  relativization : BarrierStatus
  naturalProofs : BarrierStatus
  algebrization : BarrierStatus
  note : String

inductive OrientedMaterial
    {Language : Type}
    (P NP : Language → Prop) where
  | typeA : D P NP → OrientedMaterial P NP
  | typeB : SeparationWitness P NP → OrientedMaterial P NP

theorem oriented_material_closes_terminal
    {Language : Type}
    {P NP : Language → Prop}
    (hStart : StartClosed P NP)
    (h : OrientedMaterial P NP) :
    EqualityFinal P NP ∨ SeparationFinal P NP := by
  cases h with
  | typeA hD =>
      exact Or.inl (discriminant_implies_equality hStart hD)
  | typeB hW =>
      exact Or.inr (witness_implies_separation_final hW)

#print axioms typeA_closes_equality
#print axioms typeB_closes_separation
#print axioms oriented_material_closes_terminal

end BackwardAudit
end MCore
