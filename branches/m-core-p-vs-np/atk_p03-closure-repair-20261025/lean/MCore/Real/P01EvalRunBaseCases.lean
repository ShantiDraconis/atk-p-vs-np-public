import MCore.Real.P01EvalRunLoopRun
import MCore.Real.P01EvalRunInputTag
import MCore.Real.P01EvalRunHaveValue
import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace P01EvalRunBaseCases

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01NTMRunLaws
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalRunLoopNTM
open P01EvalRunLoopRun
open P01EvalRunInputTag
open P01EvalRunHaveValue

abbrev LoopConfig :=
  Configuration EvalRunLoopState (Option Bool)

/-- Top-level physical execution of the encoded constant-false circuit reaches
the global accepting final state. -/
theorem constFalse_encode_reaches_final
    (witness : BitString)
    (padding : Nat) :
    ∃ m ≤ constLoopFuel [] [] + 2,
      ({ state := .final false,
         tape := evalCursorStackEndTape witness 3 [] [] padding } :
        LoopConfig) ∈
      evalRunLoopMachine.runBranches m
        [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness 0
               (encodeCircuit (.const false)) [] padding }] := by
  obtain ⟨m1, hm1, h1⟩ :=
    constFalse_loop_reaches_have witness [] [] 0 padding
  obtain ⟨m2, hm2, h2⟩ :=
    emptyFrames_loop_reaches_final witness [] 3 padding false
  have h :=
    mem_runBranches_trans evalRunLoopMachine
      m1 m2
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness 0
             (false :: false :: true :: []) [] padding }]
      ({ state := .have (.start false),
         tape := evalCursorStackEndTape witness 3 [] [] padding } :
        LoopConfig)
      ({ state := .final false,
         tape := evalCursorStackEndTape witness 3 [] [] padding } :
        LoopConfig)
      h1 h2
  refine ⟨m1 + m2, by omega, ?_⟩
  simpa [encodeCircuit] using h

/-- Top-level physical execution of the encoded constant-true circuit reaches
the global accepting final state. -/
theorem constTrue_encode_reaches_final
    (witness : BitString)
    (padding : Nat) :
    ∃ m ≤ constLoopFuel [] [] + 2,
      ({ state := .final true,
         tape := evalCursorStackEndTape witness 3 [] [] padding } :
        LoopConfig) ∈
      evalRunLoopMachine.runBranches m
        [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness 0
               (encodeCircuit (.const true)) [] padding }] := by
  obtain ⟨m1, hm1, h1⟩ :=
    constTrue_loop_reaches_have witness [] [] 0 padding
  obtain ⟨m2, hm2, h2⟩ :=
    emptyFrames_loop_reaches_final witness [] 3 padding true
  have h :=
    mem_runBranches_trans evalRunLoopMachine
      m1 m2
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness 0
             (false :: true :: false :: []) [] padding }]
      ({ state := .have (.start true),
         tape := evalCursorStackEndTape witness 3 [] [] padding } :
        LoopConfig)
      ({ state := .final true,
         tape := evalCursorStackEndTape witness 3 [] [] padding } :
        LoopConfig)
      h1 h2
  refine ⟨m1 + m2, by omega, ?_⟩
  simpa [encodeCircuit] using h

/-- On the canonical finite witness, the physical indexed read agrees exactly
with the semantic assignment at the unique input variable. -/
theorem witnessBits_getD_input
    (i : Nat)
    (w : SATWitness (.input i)) :
    (witnessBits w).getD i false =
      assignmentOfWitness (.input i) w i := by
  induction i with
  | zero =>
      simp [witnessBits, assignmentOfWitness, varBound]
  | succ i ih =>
      let w' : SATWitness (.input i) := fun j => w j.succ
      have h := ih w'
      simpa [witnessBits, assignmentOfWitness, varBound, w'] using h

/-- Top-level physical execution of an encoded input node reaches the global
final state carrying exactly the semantic assignment value. -/
theorem input_encode_reaches_final
    (i : Nat)
    (w : SATWitness (.input i))
    (padding : Nat) :
    ∃ m ≤ inputTagLoopFuel 0 i [] [],
      ∃ tape : Tape (Option Bool),
        ({ state := .final (assignmentOfWitness (.input i) w i),
           tape := tape } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape (witnessBits w) 0
                 (encodeCircuit (.input i)) [] padding }] := by
  have hi : i < (witnessBits w).length := by
    rw [witnessBits_length]
    simp [varBound]
  obtain ⟨m, hm, h⟩ :=
    inputTag_empty_reaches_final
      (witnessBits w) 0 padding i hi
  refine ⟨m, hm, ?_⟩
  refine ⟨(P01InputNodeRoundTrip.inputAfterReadTarget
      (witnessBits w)
      (P01InputNodeRoundTrip.consumedAfterInputIndex 3 i)
      [] [] padding).tape, ?_⟩
  rw [witnessBits_getD_input i w] at h
  simpa [encodeCircuit] using h

#print axioms MCore.Real.P01EvalRunBaseCases.constFalse_encode_reaches_final
#print axioms MCore.Real.P01EvalRunBaseCases.constTrue_encode_reaches_final
#print axioms MCore.Real.P01EvalRunBaseCases.witnessBits_getD_input
#print axioms MCore.Real.P01EvalRunBaseCases.input_encode_reaches_final

end P01EvalRunBaseCases
end Real
end MCore
