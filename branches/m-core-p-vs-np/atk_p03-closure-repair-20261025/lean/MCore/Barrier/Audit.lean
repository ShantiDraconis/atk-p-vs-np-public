import MCore.BackwardAudit.OrientedWitnessBoundary

namespace MCore
namespace Barrier

open BackwardAudit

/-- Human-readable audit state for one representation/language.

This structure is metadata only.  In particular, a status does not prove a
complexity lower bound and cannot be consumed as `not_in_p`. -/
structure BarrierAudit where
  langName : String
  relativization : BarrierStatus := .notAssessed
  naturalProofs : BarrierStatus := .notAssessed
  algebrization : BarrierStatus := .notAssessed
  note : String := ""
  deriving Repr

/-- Fail-closed default: an unaudited language starts with no escape claim. -/
def auditHonestNotAssessed (name : String) : BarrierAudit :=
  { langName := name }

/-- Current Boolean/TM lane audit.

The present finite-control simulation machinery appears to relativize, but
this is metadata only; no barrier escape is claimed. -/
def auditGapRead : BarrierAudit :=
  { langName := "Bool + preserving gap/read"
    relativization := .appearsToRelativize
    naturalProofs := .notAssessed
    algebrization := .notAssessed
    note :=
      "Metadata only: current det-step/shuttle/seq/relabel constructions do not constitute a proved barrier escape." }

/-- Formal meanings for the three escape claims of a chosen technique type.

No concrete predicates are supplied here.  A later barrier formalization must
define these propositions before checked escape evidence can exist. -/
structure BarrierPredicates (Technique : Type) where
  NonRelativizing : Technique → Prop
  NonNaturalizing : Technique → Prop
  NonAlgebrizing : Technique → Prop

/-- Checked escape evidence.

The three fields are Lean proof terms, not Boolean flags or documentation
strings.  Consequently a literature citation alone cannot inhabit this type.

This object still does NOT imply `G21Pointwise`; it only certifies the three
predicates supplied by a formal barrier model. -/
structure EscapeEvidence
    {Technique : Type}
    (B : BarrierPredicates Technique) where
  technique : Technique
  nonRelativizing : B.NonRelativizing technique
  nonNaturalizing : B.NonNaturalizing technique
  nonAlgebrizing : B.NonAlgebrizing technique
  proofRefs : List String := []

/-- Checked evidence may be rendered as audit metadata.

The conversion is deliberately one-way: this file contains no conversion from
`BarrierAudit` back to `EscapeEvidence`, and no conversion from either type
to a lower-bound witness. -/
def EscapeEvidence.toAudit
    {Technique : Type}
    {B : BarrierPredicates Technique}
    (_E : EscapeEvidence B)
    (name : String) : BarrierAudit :=
  { langName := name
    relativization := .evidenceOfEscape
    naturalProofs := .evidenceOfEscape
    algebrization := .evidenceOfEscape
    note :=
      "Statuses backed by Lean proof fields in EscapeEvidence; proofRefs remain documentation only." }

/-- Merely having an audit record leaves the actual separation proposition
unchanged.  This is a small fail-closed sanity theorem: the audit can always be
discarded without yielding mathematical content. -/
theorem audit_erases
    (A : BarrierAudit) (P : Prop) :
    P → P := by
  intro h
  exact h

#print axioms MCore.Barrier.auditHonestNotAssessed
#print axioms MCore.Barrier.auditGapRead
#print axioms MCore.Barrier.EscapeEvidence.toAudit
#print axioms MCore.Barrier.audit_erases

end Barrier
end MCore
