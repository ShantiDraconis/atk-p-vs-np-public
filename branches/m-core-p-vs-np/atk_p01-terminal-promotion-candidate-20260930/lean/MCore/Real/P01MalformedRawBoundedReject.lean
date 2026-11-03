import MCore.Real.P01CheckedEvalRejectBounded
import MCore.Real.P01ExactBoundedAll
import MCore.Real.P01CheckedEvalRunBaseCases
import MCore.Real.P01MaterialGlobalBudget
import MCore.Real.P01DecodeCoreLaws

namespace MCore
namespace Real
namespace P01MalformedRawBoundedReject

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open CircuitK1
open P01CNFMode
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunBoundedHelpers
open P01CheckedEvalRunBoundedCertificate
open P01CheckedVerifierInvariant
open P01CheckedEvalRejectBounded
open P01ExactBoundedAll
open P01MaterialGlobalBudget
open P01NTMRunLaws
open P01DecodeCoreLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Exact decomposition of top-level decoder failure.

Either the recursive decoder itself returns none, or it successfully decodes
one canonical circuit but leaves a nonempty source suffix. -/
theorem decodeCircuit_none_split
    (bs : BitString)
    (h : decodeCircuit bs = none) :
    decodeCircuitCore (bs.length + 1) bs = none ∨
      ∃ phi b rest,
        decodeCircuitCore (bs.length + 1) bs =
          some (phi, b :: rest) := by
  unfold decodeCircuit at h
  cases hc : decodeCircuitCore (bs.length + 1) bs with
  | none =>
      exact Or.inl hc
  | some p =>
      rcases p with ⟨phi, tail⟩
      cases tail with
      | nil =>
          simp [hc] at h
      | cons b rest =>
          exact Or.inr ⟨phi, b, rest, hc⟩

/-- The checked evaluator's integrated source guard rejects a nonempty unread
source in exactly three physical steps after the semantic value has been
produced and the continuation stack is empty. -/
theorem checked_nonempty_source_reaches_reject
    (mode : SyntaxMode)
    (witness : BitString)
    (consumed padding : Nat)
    (v b : Bool)
    (rest : BitString) :
    ∃ m ≤ 3,
      ({ state := .reject,
         tape :=
           Tape.move none .left
             (Tape.move none .left
               (evalCursorStackEndTape witness consumed
                 (b :: rest) [] padding)) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start v),
             tape :=
               evalCursorStackEndTape witness consumed
                 (b :: rest) [] padding }] := by
  let t0 :=
    evalCursorStackEndTape witness consumed (b :: rest) [] padding
  let tPeek := Tape.move none .left t0
  let tCheck := Tape.move none .left tPeek
  let c0 : CheckedConfig := { state := .have mode (.start v), tape := t0 }
  let cPeek : CheckedConfig := { state := .have mode (.peek v), tape := tPeek }
  let cCheck : CheckedConfig := { state := .checkSource v, tape := tCheck }
  let cReject : CheckedConfig := { state := .reject, tape := tCheck }

  have hStartSucc :
      cPeek ∈ checkedEvalRunLoopMachine.successors c0 := by
    dsimp [c0, cPeek, tPeek, t0]
    simp [checkedEvalRunLoopMachine,
      P01HaveValueCompositeNTM.haveValueCompositeMachine,
      P01CheckedEvalRunLoopNTM.haveCheckedEmbed,
      NTM.successors, NTM.stepBranch,
      evalCursorStackEndTape, Tape.write, Tape.move,
      List.reverse_cons, List.map_append, List.append_assoc]

  have hStart :
      cPeek ∈ checkedEvalRunLoopMachine.runBranches 1 [c0] := by
    have h :=
      mem_runBranches_succ_of_successor
        checkedEvalRunLoopMachine 0 [c0] c0 cPeek
        (by simp [NTM.runBranches])
        (by
          dsimp [c0]
          simp [Halted, checkedEvalRunLoopMachine])
        hStartSucc
    simpa using h

  have hPeekSucc :
      cCheck ∈ checkedEvalRunLoopMachine.successors cPeek := by
    dsimp [cPeek, cCheck, tPeek, tCheck, t0]
    simp [checkedEvalRunLoopMachine, evalCursorStackEndTape,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move,
      List.reverse_cons, List.map_append, List.append_assoc]

  have hPeek :
      cCheck ∈ checkedEvalRunLoopMachine.runBranches 1 [cPeek] := by
    have h :=
      mem_runBranches_succ_of_successor
        checkedEvalRunLoopMachine 0 [cPeek] cPeek cCheck
        (by simp [NTM.runBranches])
        (by
          dsimp [cPeek]
          simp [Halted, checkedEvalRunLoopMachine])
        hPeekSucc
    simpa using h

  have hCheckSucc :
      cReject ∈ checkedEvalRunLoopMachine.successors cCheck := by
    dsimp [cCheck, cReject, tCheck, tPeek, t0]
    cases hrev : rest.reverse with
    | nil =>
        have hrest : rest = [] := by
          simpa using hrev
        subst rest
        cases b <;> cases consumed <;>
          simp [checkedEvalRunLoopMachine, evalCursorStackEndTape,
            NTM.successors, NTM.stepBranch, Halted,
            Tape.write, Tape.move, List.reverse_cons,
            List.map_append, List.replicate_succ,
            List.append_assoc]
    | cons x xs =>
        cases x <;> cases b <;> cases consumed <;>
          simp [checkedEvalRunLoopMachine, evalCursorStackEndTape,
            NTM.successors, NTM.stepBranch, Halted,
            Tape.write, Tape.move, List.reverse_cons,
            List.map_append, hrev, List.replicate_succ,
            List.append_assoc]

  have hCheck :
      cReject ∈ checkedEvalRunLoopMachine.runBranches 1 [cCheck] := by
    have h :=
      mem_runBranches_succ_of_successor
        checkedEvalRunLoopMachine 0 [cCheck] cCheck cReject
        (by simp [NTM.runBranches])
        (by
          dsimp [cCheck]
          simp [Halted, checkedEvalRunLoopMachine])
        hCheckSucc
    simpa using h

  have h01 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      1 1 [c0] cPeek cCheck hStart hPeek
  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      2 1 [c0] cCheck cReject h01 hCheck
  refine ⟨3, by omega, ?_⟩
  dsimp [c0, cReject, t0, tPeek, tCheck] at hAll ⊢
  simpa using hAll

theorem checked_nonempty_source_reaches_reject_within_envelope
    (n : Nat)
    (mode : SyntaxMode)
    (witness : BitString)
    (consumed padding : Nat)
    (v b : Bool)
    (rest : BitString) :
    ∃ m ≤ checkedLoopStepEnvelope n,
      ({ state := .reject,
         tape :=
           Tape.move none .left
             (Tape.move none .left
               (evalCursorStackEndTape witness consumed
                 (b :: rest) [] padding)) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start v),
             tape :=
               evalCursorStackEndTape witness consumed
                 (b :: rest) [] padding }] := by
  obtain ⟨m, hm, hrun⟩ :=
    checked_nonempty_source_reaches_reject
      mode witness consumed padding v b rest
  refine ⟨m, Nat.le_trans hm ?_, hrun⟩
  exact Nat.le_trans (by omega : 3 ≤ 9)
    (nine_le_stepEnvelope n)

/-- If the recursive decoder succeeds but leaves a nonempty suffix, then the
checked physical evaluator rejects the raw source.  If the decoded circuit
violates CNF, rejection is structural; otherwise the exact bounded evaluator
produces its Boolean and the mandatory source-empty guard rejects the suffix. -/
theorem core_success_with_trailing_reaches_reject_bounded
    (witness bs : BitString)
    (phi : Circuit)
    (b : Bool) (rest : BitString)
    (hw : witness.length = bs.length)
    (hcore :
      decodeCircuitCore (bs.length + 1) bs =
        some (phi, b :: rest)) :
    ∃ m ≤ checkedCircuitBudget phi bs.length +
          checkedLoopStepEnvelope bs.length,
      ∃ cfg,
        cfg ∈
          checkedEvalRunLoopMachine.runBranches m
            [{ state := .need .cnf needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness 0 bs [] 0 }] ∧
        cfg.state = .reject := by
  have hsource :
      bs = encodeCircuit phi ++ (b :: rest) :=
    decodeCircuitCore_sound _ bs phi (b :: rest) hcore
  have hencLen :
      (encodeCircuit phi).length ≤ bs.length := by
    rw [hsource]
    simp
  have hlen :
      varBound phi ≤ witness.length := by
    have hv := varBound_le_encoded_length phi
    rw [hw]
    exact Nat.le_trans hv hencLen
  let sigma : Assignment := fun i => witness.getD i false
  have hread :
      ∀ i, i < varBound phi →
        witness.getD i false = sigma i := by
    intro i hi
    rfl
  have hLayout :
      CheckedLayoutBound bs.length 0
        (encodeCircuit phi ++ (b :: rest)) [] := by
    simpa [hsource] using
      (CheckedLayoutBound.root bs)

  cases hmode : modeCheck .cnf phi with
  | false =>
      obtain ⟨m, hm, cfg, hrun, hrej⟩ :=
        bounded_circuit_reject_certificate sigma witness phi .cnf
          hmode (b :: rest) [] 0 0 bs.length
          hLayout hlen hread
      refine ⟨m, ?_, cfg, ?_, hrej⟩
      · exact Nat.le_trans hm (Nat.le_add_right _ _)
      · simpa [hsource] using hrun
  | true =>
      obtain ⟨m0, hm0, cfg0, h0, hout0⟩ :=
        exact_bounded_all sigma witness phi .cnf
          hmode (b :: rest) [] 0 0 bs.length
          hLayout hlen hread
      have hout0' :
          ∃ padding0,
            cfg0 =
              { state := .have (exitMode .cnf phi)
                  (.start (evalCircuit sigma phi)),
                tape :=
                  evalCursorStackEndTape witness
                    (encodeCircuit phi).length
                    (b :: rest) [] padding0 } := by
        simpa [ExactCheckedLoopOutcome] using hout0
      rcases hout0' with ⟨padding0, hcfg0⟩
      subst cfg0
      obtain ⟨m1, hm1, h1⟩ :=
        checked_nonempty_source_reaches_reject_within_envelope
          bs.length (exitMode .cnf phi) witness
          (encodeCircuit phi).length padding0
          (evalCircuit sigma phi) b rest
      let cfgReject : CheckedConfig :=
        { state := .reject,
          tape :=
            Tape.move none .left
              (Tape.move none .left
                (evalCursorStackEndTape witness
                  (encodeCircuit phi).length
                  (b :: rest) [] padding0)) }
      have h1' :
          cfgReject ∈
            checkedEvalRunLoopMachine.runBranches m1
              [{ state := .have (exitMode .cnf phi)
                   (.start (evalCircuit sigma phi)),
                 tape :=
                   evalCursorStackEndTape witness
                     (encodeCircuit phi).length
                     (b :: rest) [] padding0 }] := by
        simpa [cfgReject] using h1
      have hAll :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          m0 m1
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness 0
                 (encodeCircuit phi ++ (b :: rest)) [] 0 }]
          ({ state := .have (exitMode .cnf phi)
               (.start (evalCircuit sigma phi)),
             tape :=
               evalCursorStackEndTape witness
                 (encodeCircuit phi).length
                 (b :: rest) [] padding0 } : CheckedConfig)
          cfgReject h0 h1'
      refine ⟨m0 + m1, ?_, cfgReject, ?_, rfl⟩
      · omega
      · simpa [hsource] using hAll


/-- One extra checked-loop envelope after a complete circuit evaluation still
fits the material 8192-cubic verifier budget. -/
theorem checkedCircuitBudget_plus_loop_le_material
    (n : Nat) (phi : Circuit)
    (henc : (encodeCircuit phi).length ≤ n) :
    checkedCircuitBudget phi n + checkedLoopStepEnvelope n ≤
      materialVerifierGlobalTimeBound n := by
  have heval := checkedCircuitBudget_le_6144_cubic n phi henc
  have hloop :
      checkedLoopStepEnvelope n ≤ 256 * (n + 1) ^ 3 := by
    unfold checkedLoopStepEnvelope
    have h1 : 1 ≤ n + 1 := by omega
    have hpow : (n + 1)^2 ≤ (n + 1)^3 := by
      rw [Nat.pow_succ]
      exact Nat.le_mul_of_pos_right _ h1
    exact Nat.mul_le_mul_left 256 hpow
  unfold materialVerifierGlobalTimeBound
  calc
    checkedCircuitBudget phi n + checkedLoopStepEnvelope n
        ≤ 6144 * (n + 1)^3 + 256 * (n + 1)^3 :=
          Nat.add_le_add heval hloop
    _ ≤ 8192 * (n + 1)^3 := by
          exact Nat.mul_le_mul_right ((n + 1)^3) (by omega)

/-- Full evaluator-level malformed-source reduction.

Once recursive core-decoder failure is physically rejected, every raw source
whose total decoder returns none is rejected within the same global material
bound.  The other possible decoder failure -- a successfully decoded circuit
with trailing garbage -- is already physically closed above. -/
theorem malformed_raw_reaches_reject_bounded_of_core
    (K : CoreDecodeFailurePhysicalReject)
    (witness bs : BitString)
    (hw : witness.length = bs.length)
    (hdecode : decodeCircuit bs = none) :
    ∃ m ≤ materialVerifierGlobalTimeBound bs.length, ∃ cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape := evalCursorStackEndTape witness 0 bs [] 0 }] ∧
      cfg.state = .reject := by
  rcases decodeCircuit_none_split bs hdecode with hcore | htrail
  · exact K witness bs hw hcore
  · rcases htrail with ⟨phi, b, rest, hcore⟩
    obtain ⟨m, hm, cfg, hrun, hrej⟩ :=
      core_success_with_trailing_reaches_reject_bounded
        witness bs phi b rest hw hcore
    have hsource :
        bs = encodeCircuit phi ++ (b :: rest) :=
      decodeCircuitCore_sound _ bs phi (b :: rest) hcore
    have henc : (encodeCircuit phi).length ≤ bs.length := by
      rw [hsource]
      simp
    exact ⟨m,
      Nat.le_trans hm
        (checkedCircuitBudget_plus_loop_le_material bs.length phi henc),
      cfg, hrun, hrej⟩

/-- After closing the trailing-garbage branch, the only raw-decoder case not
yet supplied by existing physical certificates is recursive core failure. -/
def CoreDecodeFailurePhysicalReject : Prop :=
  ∀ (witness bs : BitString),
    witness.length = bs.length →
    decodeCircuitCore (bs.length + 1) bs = none →
    ∃ m ≤ materialVerifierGlobalTimeBound bs.length, ∃ cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape := evalCursorStackEndTape witness 0 bs [] 0 }] ∧
      cfg.state = .reject

#print axioms MCore.Real.P01MalformedRawBoundedReject.decodeCircuit_none_split
#print axioms MCore.Real.P01MalformedRawBoundedReject.checked_nonempty_source_reaches_reject
#print axioms MCore.Real.P01MalformedRawBoundedReject.core_success_with_trailing_reaches_reject_bounded
#print axioms MCore.Real.P01MalformedRawBoundedReject.checkedCircuitBudget_plus_loop_le_material
#print axioms MCore.Real.P01MalformedRawBoundedReject.malformed_raw_reaches_reject_bounded_of_core

end P01MalformedRawBoundedReject
end Real
end MCore
