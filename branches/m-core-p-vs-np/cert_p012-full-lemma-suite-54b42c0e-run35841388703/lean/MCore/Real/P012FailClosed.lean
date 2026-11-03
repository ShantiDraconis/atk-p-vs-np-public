import MCore.Real.P01FinalCertificate
import MCore.Real.P02G21G22Attack
import MCore.Real.FinalExternalTwoGap
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace P012FailClosed

open CanonicalFinalProof
open P01FinalCertificate
open P02G21G22Attack
open FinalExternalTwoGap
open FinalExternalCertificate
open OfficialModel

/-- Three fail-closed progress states for the two terminal producers. -/
inductive P012
| zero
| partial
| closed
deriving DecidableEq, Repr

/-- Exact Boolean accounting for the two terminal producers. -/
def progress (p01 g21 : Bool) : P012 :=
  match p01, g21 with
  | false, false => .zero
  | true,  true  => .closed
  | _,     _     => .partial

@[simp] theorem progress_false_false :
    progress false false = .zero := rfl

@[simp] theorem progress_true_false :
    progress true false = .partial := rfl

@[simp] theorem progress_false_true :
    progress false true = .partial := rfl

@[simp] theorem progress_true_true :
    progress true true = .closed := rfl

/-- The rigid core is exactly the conjunction already used by FinalExternalTwoGap. -/
abbrev RigidCore : Prop :=
  P01ConstructionGap ∧ G21Pointwise

theorem rigidCore_iff_finalExternalTwoGap :
    RigidCore ↔ FinalExternalTwoGap := by
  rfl

/-- 1/1: both terminal producers inhabit the rigid core. -/
def one_one
    (hP01 : P01ConstructionGap)
    (hG21 : G21Pointwise) :
    FinalExternalTwoGap :=
  ⟨hP01, hG21⟩

/-- A P01-only state cannot be promoted by this constructor; the G21 proof
must still be supplied explicitly. -/
def zero_one_to_one_one
    (hP01 : P01ConstructionGap)
    (hG21 : G21Pointwise) :
    RigidCore :=
  ⟨hP01, hG21⟩

/-- Once at 1/1, the existing certified wiring yields FinalExternalGap. -/
theorem one_one_to_final_gap
    (h : RigidCore) :
    FinalExternalGap :=
  final_external_gap_of_two_gap h

/-- Once at 1/1, no additional mathematical producer is needed for the
official external separation statement. -/
theorem one_one_to_official
    (h : RigidCore) :
    ∃ S : OfficialModelSelection,
      OfficialPneqNP S.model.P S.model.NP :=
  final_external_two_gap_closes h

/-- Idempotence of the rigid core: once both producers are present, rebuilding
the pair does not change the logical state. -/
theorem one_one_idempotent
    (h : RigidCore) :
    (⟨h.1, h.2⟩ : RigidCore) = h := by
  cases h
  rfl

/-- Fail-closed AND law: closure is equivalent to both producer propositions. -/
theorem rigidCore_iff_and :
    RigidCore ↔ (P01ConstructionGap ∧ G21Pointwise) := by
  rfl

#print axioms MCore.Real.P012FailClosed.rigidCore_iff_finalExternalTwoGap
#print axioms MCore.Real.P012FailClosed.one_one_to_final_gap
#print axioms MCore.Real.P012FailClosed.one_one_to_official
#print axioms MCore.Real.P012FailClosed.one_one_idempotent
#print axioms MCore.Real.P012FailClosed.rigidCore_iff_and

end P012FailClosed
end Real
end MCore
