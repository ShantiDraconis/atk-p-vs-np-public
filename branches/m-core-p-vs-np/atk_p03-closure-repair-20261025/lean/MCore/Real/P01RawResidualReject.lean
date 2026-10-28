import MCore.Real.P01ExactBoundedCircuitProducer
import MCore.Real.P01RawVerifierLift
import MCore.Real.P01ExactVerifierGlobalBudget

namespace MCore
namespace Real
namespace P01RawResidualReject

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01EncodedFrameTape
open P01HaveValueCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedVerifierInvariant
open P01CheckedEvalRunBoundedCertificate
open P01ExactBoundedCircuitProducer
open P01RawVerifierLift
open P01NTMRunLaws

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

private theorem one_step_of_successor
    (a b : EvalConfig)
    (ha : ¬ Halted checkedEvalRunLoopMachine a)
    (hs : b ∈ checkedEvalRunLoopMachine.successors a) :
    b ∈ checkedEvalRunLoopMachine.runBranches 1 [a] := by
  have h :=
    mem_runBranches_succ_of_successor
      checkedEvalRunLoopMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

/-- With no continuation frames, a nonempty unread source is rejected by the
checked loop's mandatory source-empty guard in exactly three physical steps. -/
theorem nonempty_tail_empty_frames_reaches_reject
    (mode : P01CNFMode.SyntaxMode)
    (witness : BitString)
    (consumed padding : Nat)
    (b : Bool) (bs : BitString)
    (v : Bool) :
    ∃ m ≤ 3,
      ({ state := .reject,
         tape :=
           Tape.move none .left
             (Tape.move none .left
               (evalCursorStackEndTape witness consumed (b :: bs) [] padding)) } :
        EvalConfig) ∈
      checkedEvalRunLoopMachine.runBranches m
        [{ state := .have mode (.start v),
           tape :=
             evalCursorStackEndTape witness consumed (b :: bs) [] padding }] := by
  let t0 := evalCursorStackEndTape witness consumed (b :: bs) [] padding
  let tPeek := Tape.move none .left t0
  let tCheck := Tape.move none .left tPeek
  let c0 : EvalConfig := { state := .have mode (.start v), tape := t0 }
  let cPeek : EvalConfig := { state := .have mode (.peek v), tape := tPeek }
  let cCheck : EvalConfig := { state := .checkSource v, tape := tCheck }
  let cReject : EvalConfig := { state := .reject, tape := tCheck }

  have hStartSucc :
      cPeek ∈ checkedEvalRunLoopMachine.successors c0 := by
    dsimp [c0, cPeek, tPeek, t0]
    simp [checkedEvalRunLoopMachine, haveValueCompositeMachine,
      haveCheckedEmbed, NTM.successors, NTM.stepBranch,
      evalCursorStackEndTape, Tape.write, Tape.move,
      List.append_assoc]

  have hStart :
      cPeek ∈ checkedEvalRunLoopMachine.runBranches 1 [c0] :=
    one_step_of_successor c0 cPeek
      (by dsimp [c0]; simp [Halted, checkedEvalRunLoopMachine])
      hStartSucc

  have hPeekSucc :
      cCheck ∈ checkedEvalRunLoopMachine.successors cPeek := by
    dsimp [cPeek, cCheck, tPeek, tCheck, t0]
    simp [checkedEvalRunLoopMachine, evalCursorStackEndTape,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move,
      List.reverse_cons, List.map_append, List.append_assoc]

  have hPeek :
      cCheck ∈ checkedEvalRunLoopMachine.runBranches 1 [cPeek] :=
    one_step_of_successor cPeek cCheck
      (by dsimp [cPeek]; simp [Halted, checkedEvalRunLoopMachine])
      hPeekSucc

  have hRejectSucc :
      cReject ∈ checkedEvalRunLoopMachine.successors cCheck := by
    have hrevne : (b :: bs).reverse ≠ [] := by
      simp
    cases hrev : (b :: bs).reverse with
    | nil =>
        exact False.elim (hrevne hrev)
    | cons r rs =>
        dsimp [cCheck, cReject, tCheck, tPeek, t0]
        simp [checkedEvalRunLoopMachine, evalCursorStackEndTape,
          NTM.successors, NTM.stepBranch, Tape.write, Tape.move,
          hrev, List.map_append, List.replicate_succ,
          List.append_assoc]

  have hReject :
      cReject ∈ checkedEvalRunLoopMachine.runBranches 1 [cCheck] :=
    one_step_of_successor cCheck cReject
      (by dsimp [cCheck]; simp [Halted, checkedEvalRunLoopMachine])
      hRejectSucc

  have h01 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      1 1 [c0] cPeek cCheck hStart hPeek
  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      2 1 [c0] cCheck cReject h01 hReject
  refine ⟨3, by omega, ?_⟩
  dsimp [c0, cReject, t0, tPeek, tCheck] at hAll ⊢
  simpa using hAll

/-- Exact bounded evaluation of a valid canonical CNF prefix followed by
nonempty garbage reaches physical reject. -/
theorem canonical_prefix_with_residual_reaches_reject
    (sigma : Assignment)
    (witness : BitString)
    (phi : Circuit)
    (tail : BitString)
    (hne : tail ≠ [])
    (hmode : modeCheck .cnf phi = true)
    (n : Nat)
    (hLayout :
      CheckedLayoutBound n 0
        (encodeCircuit phi ++ tail) (encodeEvalFrames []))
    (hlen : varBound phi ≤ witness.length)
    (hread :
      ∀ i, i < varBound phi →
        witness.getD i false = sigma i) :
    ∃ m ≤ checkedCircuitBudget phi n + 3, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := checkedEvalRunLoopMachine.initial,
           tape :=
             evalCursorStackEndTape witness 0
               (encodeCircuit phi ++ tail) [] 0 }] ∧
      cfg.state = .reject := by
  have hcert := circuit_exact_bounded_certificate sigma witness phi .cnf
  obtain ⟨m0, hm0, cfg0, h0, hout0⟩ :=
    hcert hmode tail [] 0 0 n hLayout hlen hread
  obtain ⟨padding0, hcfg0⟩ :=
    exact_outcome_have_of_tail_ne_nil
      witness (exitMode .cnf phi) (evalCircuit sigma phi)
      tail [] (encodeCircuit phi).length cfg0 hne
      (by simpa using hout0)
  subst cfg0
  cases tail with
  | nil => exact False.elim (hne rfl)
  | cons b bs =>
      obtain ⟨m1, hm1, h1⟩ :=
        nonempty_tail_empty_frames_reaches_reject
          (exitMode .cnf phi) witness (encodeCircuit phi).length
          padding0 b bs (evalCircuit sigma phi)
      let cReject : EvalConfig :=
        { state := .reject,
          tape :=
            Tape.move none .left
              (Tape.move none .left
                (evalCursorStackEndTape witness (encodeCircuit phi).length
                  (b :: bs) [] padding0)) }
      have hAll :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          m0 m1
          [{ state := checkedEvalRunLoopMachine.initial,
             tape :=
               evalCursorStackEndTape witness 0
                 (encodeCircuit phi ++ (b :: bs)) [] 0 }]
          ({ state := .have (exitMode .cnf phi)
               (.start (evalCircuit sigma phi)),
             tape :=
               evalCursorStackEndTape witness (encodeCircuit phi).length
                 (b :: bs) [] padding0 } : EvalConfig)
          cReject
          (by simpa using h0)
          (by simpa [cReject] using h1)
      refine ⟨m0 + m1, by omega, cReject, hAll, rfl⟩

#print axioms MCore.Real.P01RawResidualReject.nonempty_tail_empty_frames_reaches_reject
#print axioms MCore.Real.P01RawResidualReject.canonical_prefix_with_residual_reaches_reject

end P01RawResidualReject
end Real
end MCore
