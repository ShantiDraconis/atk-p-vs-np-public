import Mathlib.Computability.Halting
import MCore.Real.P02CodeSemanticInput

namespace MCore
namespace Real
namespace P02SelfInputHaltingBarrier

open P02BitStringNatCoding
open P02CodeSemanticInput

def haltMarkerNat : Nat :=
  encodeBitsNat [true]

def markHalting (c : Nat.Partrec.Code) : Nat.Partrec.Code :=
  (Nat.Partrec.Code.const haltMarkerNat).comp c

theorem markHalting_computable :
    Computable markHalting := by
  exact
    (Primrec₂.comp
      Nat.Partrec.Code.primrec₂_comp
      (Primrec.const (Nat.Partrec.Code.const haltMarkerNat))
      Primrec.id).to_comp

theorem markHalting_eval_zero
    (c : Nat.Partrec.Code) :
    (markHalting c).eval 0 =
      c.eval 0 >>= fun _ => Part.some haltMarkerNat := by
  simp [markHalting, haltMarkerNat]

theorem selfInput_markHalting_iff
    (c : Nat.Partrec.Code) :
    selfInput (markHalting c) = [true] ↔
      (c.eval 0).Dom := by
  constructor
  · intro hself
    by_contra hdom
    have hcNone : c.eval 0 = Part.none :=
      (Part.eq_none_iff').2 hdom
    have hmNone : (markHalting c).eval 0 = Part.none := by
      simp [markHalting, hcNone]
    have hmNotDom : ¬((markHalting c).eval 0).Dom := by
      rw [hmNone]
      exact Part.not_none_dom
    have hEmpty : selfInput (markHalting c) = [] := by
      unfold selfInput
      rw [dif_neg hmNotDom]
    rw [hEmpty] at hself
    simp at hself
  · intro hdom
    have hcSome :
        c.eval 0 = Part.some ((c.eval 0).get hdom) := by
      symm
      exact Part.some_get hdom
    have hmSome :
        (markHalting c).eval 0 = Part.some haltMarkerNat := by
      simp [markHalting, hcSome, haltMarkerNat]
    have hmem :
        encodeBitsNat [true] ∈ (markHalting c).eval 0 := by
      rw [hmSome]
      simp [haltMarkerNat]
    exact selfInput_of_mem_encode (markHalting c) [true] hmem

/-- The extensional totalization used by the current compiler route cannot
itself be computable: otherwise it would decide the halting problem at input 0.
This is a theorem about the current definition of selfInput, not an assumption. -/
theorem selfInput_not_computable :
    ¬ Computable selfInput := by
  intro hSelf
  have hMarked :
      Computable (fun c : Nat.Partrec.Code =>
        selfInput (markHalting c)) :=
    hSelf.comp markHalting_computable
  have hEqDec :
      Computable (fun c : Nat.Partrec.Code =>
        decide (selfInput (markHalting c) = [true])) := by
    exact Primrec.eq.to_comp.comp hMarked (Computable.const [true])
  have hPred :
      ComputablePred (fun c : Nat.Partrec.Code =>
        selfInput (markHalting c) = [true]) :=
    Computable.computablePred hEqDec
  have hHalting :
      ComputablePred (fun c : Nat.Partrec.Code =>
        (c.eval 0).Dom) :=
    hPred.of_eq selfInput_markHalting_iff
  exact (ComputablePred.halting_problem 0) hHalting

#print axioms MCore.Real.P02SelfInputHaltingBarrier.markHalting_computable
#print axioms MCore.Real.P02SelfInputHaltingBarrier.selfInput_markHalting_iff
#print axioms MCore.Real.P02SelfInputHaltingBarrier.selfInput_not_computable

end P02SelfInputHaltingBarrier
end Real
end MCore
