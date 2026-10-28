import MCore.C12.Families

namespace Audit.C12Calibration

open MCore
open MCore.C9
open MCore.C11
open MCore.CircuitK1
open MCore.CircuitC2

def SemanticallyEquivalent (a b : Circuit) : Prop :=
  ∀ σ : Assignment, eval σ a = eval σ b

def paddedFalse : Nat → Circuit
  | 0 => .const false
  | n + 1 => .and (.input n) (paddedFalse n)

theorem paddedFalse_eval_false (n : Nat) (σ : Assignment) :
    eval σ (paddedFalse n) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [paddedFalse, eval, ih]

theorem paddedFalse_equiv_const_false (n : Nat) :
    SemanticallyEquivalent (paddedFalse n) (.const false) := by
  intro σ
  simp [paddedFalse_eval_false, eval]

@[simp] theorem paddedFalse_one_potential :
    Potential 1 1 (paddedFalse 1) = 10 := by
  decide

@[simp] theorem const_false_potential :
    Potential 1 1 (.const false) = 1 := by
  decide

theorem potential_not_semantic_invariant :
    ∃ a b : Circuit,
      SemanticallyEquivalent a b ∧
      Potential 1 1 a ≠ Potential 1 1 b := by
  refine ⟨paddedFalse 1, .const false, paddedFalse_equiv_const_false 1, ?_⟩
  decide

def DirectPotentialAsSemanticComplexity : Prop :=
  ∀ a b : Circuit,
    SemanticallyEquivalent a b →
      Potential 1 1 a = Potential 1 1 b

theorem direct_potential_semantic_identification_refuted :
    ¬ DirectPotentialAsSemanticComplexity := by
  intro h
  have heq :
      Potential 1 1 (paddedFalse 1) = Potential 1 1 (.const false) :=
    h (paddedFalse 1) (.const false) (paddedFalse_equiv_const_false 1)
  have hne :
      Potential 1 1 (paddedFalse 1) ≠ Potential 1 1 (.const false) := by
    decide
  exact hne heq

/-- This refutes only direct identification of raw syntactic Potential with a
semantic complexity measure.  A minimized or otherwise representation-invariant
calibration remains an open bridge. -/
def SDirectStatus : String := "REFUTED_DIRECT_PROXY_IDENTIFICATION"
def SMinimizedStatus : String := "OPEN_BRIDGE_REPRESENTATION_INVARIANT_CALIBRATION"

#print axioms Audit.C12Calibration.paddedFalse_eval_false
#print axioms Audit.C12Calibration.paddedFalse_equiv_const_false
#print axioms Audit.C12Calibration.potential_not_semantic_invariant
#print axioms Audit.C12Calibration.direct_potential_semantic_identification_refuted

end Audit.C12Calibration
