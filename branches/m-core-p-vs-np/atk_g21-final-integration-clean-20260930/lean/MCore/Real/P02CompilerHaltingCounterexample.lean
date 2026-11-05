import Mathlib.Tactic
import MCore.Real.P02EffectiveCompilerConstruction
import MCore.Real.P02SelfInputHaltingBarrier

namespace MCore
namespace Real
namespace P02CompilerHaltingCounterexample

open CanonicalFinalProof
open CanonicalCircuitBits
open P02BitStringNatCoding
open P02CodeSemanticInput
open P02CookLevinFromBoundedExec
open P02EffectiveCompilerConstruction
open P02SelfInputHaltingBarrier

def barrierMachine : TM (Fin 1) (Option Bool) where
  initial := 0
  blank := none
  transition := fun q a => (q, a, .stay)
  halting := fun _ => true

def barrierCandidate : PolyDTMCandidate where
  stateCount := 0
  machine := barrierMachine
  blank_none := rfl
  accepting := fun _ => false
  timeBound := fun _ => 0
  time_poly := by
    refine ⟨0, 0, ?_⟩
    intro n
    simp

def barrierOutEmpty : Nat :=
  encodeBitsNat
    (encodeCircuit (rejectCircuit barrierCandidate []))

def barrierOutTrue : Nat :=
  encodeBitsNat
    (encodeCircuit (rejectCircuit barrierCandidate [true]))

theorem barrier_outputs_ne :
    barrierOutEmpty ≠ barrierOutTrue := by
  decide

theorem selfInput_markHalting_eq_empty_of_not_dom
    (c : Nat.Partrec.Code)
    (hdom : ¬(c.eval 0).Dom) :
    selfInput (markHalting c) = [] := by
  have hcNone : c.eval 0 = Part.none :=
    (Part.eq_none_iff').2 hdom
  have hmNone : (markHalting c).eval 0 = Part.none := by
    simp [markHalting, hcNone]
  have hmNotDom : ¬((markHalting c).eval 0).Dom := by
    rw [hmNone]
    exact Part.not_none_dom
  unfold selfInput
  rw [dif_neg hmNotDom]

theorem compilerValue_markHalting_eq_true_iff
    (c : Nat.Partrec.Code) :
    compilerValue barrierCandidate (markHalting c) =
        barrierOutTrue ↔
      (c.eval 0).Dom := by
  constructor
  · intro hout
    by_contra hdom
    have hs :=
      selfInput_markHalting_eq_empty_of_not_dom c hdom
    have hEmpty :
        compilerValue barrierCandidate (markHalting c) =
          barrierOutEmpty := by
      simp [compilerValue, barrierOutEmpty, hs]
    exact barrier_outputs_ne (hEmpty.symm.trans hout)
  · intro hdom
    have hs :
        selfInput (markHalting c) = [true] :=
      (selfInput_markHalting_iff c).2 hdom
    simp [compilerValue, barrierOutTrue, hs]

/-- The concrete terminal compiler value is not computable for barrierCandidate:
otherwise equality with barrierOutTrue decides whether c.eval 0 halts. -/
theorem barrier_compilerValue_not_computable :
    ¬ Computable (compilerValue barrierCandidate) := by
  intro hComp
  have hMarked :
      Computable (fun c : Nat.Partrec.Code =>
        compilerValue barrierCandidate (markHalting c)) :=
    hComp.comp markHalting_computable
  have hEqDec :
      Computable (fun c : Nat.Partrec.Code =>
        decide
          (compilerValue barrierCandidate (markHalting c) =
            barrierOutTrue)) := by
    exact
      Primrec.eq.to_comp.comp hMarked
        (Computable.const barrierOutTrue)
  have hPred :
      ComputablePred (fun c : Nat.Partrec.Code =>
        compilerValue barrierCandidate (markHalting c) =
          barrierOutTrue) :=
    hEqDec.computablePred
  have hHalting :
      ComputablePred (fun c : Nat.Partrec.Code =>
        (c.eval 0).Dom) :=
    hPred.of_eq compilerValue_markHalting_eq_true_iff
  exact (ComputablePred.halting_problem 0) hHalting

/-- Falsification of the proposed terminal producer. -/
theorem uniformCompilerValueComputable_false :
    ¬ UniformCompilerValueComputable := by
  intro h
  exact barrier_compilerValue_not_computable (h barrierCandidate)

#print axioms MCore.Real.P02CompilerHaltingCounterexample.barrier_outputs_ne
#print axioms MCore.Real.P02CompilerHaltingCounterexample.barrier_compilerValue_not_computable
#print axioms MCore.Real.P02CompilerHaltingCounterexample.uniformCompilerValueComputable_false

end P02CompilerHaltingCounterexample
end Real
end MCore
