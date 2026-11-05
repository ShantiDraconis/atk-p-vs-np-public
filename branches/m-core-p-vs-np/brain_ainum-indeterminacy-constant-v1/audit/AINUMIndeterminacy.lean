import MCore.BackwardAudit.ClosedDiscriminant

namespace MCore
namespace AINUM

/-- Operational orientation state for the certified evidence layer.
This does not add a third classical truth value to P vs NP. -/
inductive OrientationState where
  | unresolved
  | equalityCertified
  | separationCertified
  | conflict
  deriving DecidableEq, Repr

/-- The fundamental AINUM constant is the fail-closed evidence state:
no orientation is promoted until a valid orientation certificate is supplied. -/
def IndeterminacyConstant : OrientationState :=
  .unresolved

structure OrientationEvidence where
  equalityCertificate : Bool
  separationCertificate : Bool
  deriving DecidableEq, Repr

def classifyEvidence (e : OrientationEvidence) : OrientationState :=
  match e.equalityCertificate, e.separationCertificate with
  | false, false => .unresolved
  | true, false => .equalityCertified
  | false, true => .separationCertified
  | true, true => .conflict

def canAutoOrient : OrientationState → Bool
  | .unresolved => false
  | .conflict => false
  | .equalityCertified => true
  | .separationCertified => true

theorem indeterminacy_blocks_auto_orientation :
    canAutoOrient IndeterminacyConstant = false := rfl

theorem empty_evidence_is_indeterminate :
    classifyEvidence ⟨false, false⟩ = IndeterminacyConstant := rfl

theorem conflicting_evidence_blocks_orientation :
    canAutoOrient (classifyEvidence ⟨true, true⟩) = false := rfl

/-- Mathematical firewall: the two genuine middle witnesses cannot coexist.
This reuses the repository's already-audited closed discriminant theorem. -/
theorem genuine_middle_branches_exclusive
    {Language : Type}
    {P NP : Language → Prop}
    (hD : ClosedDiscriminant.D P NP)
    (hW : ClosedDiscriminant.SeparationWitness P NP) :
    False :=
  ClosedDiscriminant.two_sides_false ⟨hD, hW⟩

/-- AINUM preserves the classical endpoint definitions unchanged.
The new state classifies certificate availability only. -/
structure AINUMContract (Language : Type)
    (P NP : Language → Prop) where
  startClosed : ClosedDiscriminant.StartClosed P NP
  evidence : OrientationEvidence
  noAutomaticPromotion :
    classifyEvidence evidence = .unresolved →
      canAutoOrient (classifyEvidence evidence) = false

def canonicalUnresolvedContract
    {Language : Type}
    {P NP : Language → Prop}
    (hStart : ClosedDiscriminant.StartClosed P NP) :
    AINUMContract Language P NP where
  startClosed := hStart
  evidence := ⟨false, false⟩
  noAutomaticPromotion := by
    intro _
    rfl

#print axioms MCore.AINUM.indeterminacy_blocks_auto_orientation
#print axioms MCore.AINUM.genuine_middle_branches_exclusive
#print axioms MCore.AINUM.canonicalUnresolvedContract

end AINUM
end MCore
