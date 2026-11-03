import MCore.Real.P01FinalCertificate
import MCore.Real.P02G21G22Attack
import MCore.Real.FinalProofEvidencePromotion

namespace MCore
namespace Research
namespace FinalProofGapLedger

open Real
open Real.P01FinalCertificate
open Real.P02G21G22Attack

inductive GapKind where
  | p01Construction
  | g21Pointwise
  | finalExternal
  | provenance
  | researchTransfer
  deriving DecidableEq, Repr, BEq

inductive GapState where
  | sourcePresent
  | needsVerifiedClosure
  | openMath
  | redBlocked
  | green
  | frozen
  | certified
  deriving DecidableEq, Repr, BEq

structure GapRecord where
  kind : GapKind
  state : GapState
  source : String
  note : String
  deriving Repr

/-- Exact P01 terminal proposition; the ledger never weakens it. -/
abbrev P01ExactGap : Prop := P01ConstructionGap

/-- Exact G21 terminal proposition; the ledger never replaces it by a proxy. -/
abbrev G21ExactGap : Prop := G21Pointwise

structure ExactTwoGapClosure where
  p01 : P01ExactGap
  g21 : G21ExactGap

theorem exactTwoGapClosure_producers
    (C : ExactTwoGapClosure) :
    P01ConstructionGap ∧ G21Pointwise :=
  ⟨C.p01, C.g21⟩

theorem exactTwoGapClosure_internal
    (C : ExactTwoGapClosure) :
    Real.CanonicalFinalProof.PneqNP := by
  exact Real.P02G21G22Attack.p01_g21_closes_internal
    (Real.P01FinalCertificate.construction_closes_p01 C.p01)
    C.g21

/-- A textual/detected gap record alone carries no mathematical closure. -/
def GapRecord.proofCredit (_ : GapRecord) : Nat := 0

/-
No constructor from GapRecord to P01ConstructionGap or G21Pointwise exists.
The automated comparator may discover obligations, discrepancies, and patterns,
but only ExactTwoGapClosure contains the actual proof objects.
-/

#print axioms MCore.Research.FinalProofGapLedger.exactTwoGapClosure_internal

end FinalProofGapLedger
end Research
end MCore
