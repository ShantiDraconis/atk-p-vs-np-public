import MCore.Real.P01CheckedEvalRunBaseCases
import MCore.Real.P01InputNodeCompositeRun
import MCore.Real.P01InputNodeRoundTrip

namespace MCore
namespace Real
namespace P01CheckedEvalRunInputTag

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01NTMRunLaws
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01NeedExprTagDecode
open P01InputNodeCompositeNTM
open P01InputNodeCompositeRun
open P01InputNodeRoundTrip
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix
open P01CheckedEvalRunBaseCases
open P01CNFMode

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

def inputCheckedConfig
    (mode : SyntaxMode)
    (c : Configuration InputNodeCompositeState (Option Bool)) :
    CheckedConfig :=
  { state := inputCheckedEmbed mode c.state
    tape := c.tape }

/-- Active input-node states embed exactly into the checked evaluator. -/
theorem inputChecked_successors_active
    (mode : SyntaxMode)
    (c : Configuration InputNodeCompositeState (Option Bool))
    (h : ¬ Halted inputNodeCompositeMachine c) :
    checkedEvalRunLoopMachine.successors (inputCheckedConfig mode c) =
      (inputNodeCompositeMachine.successors c).map
        (inputCheckedConfig mode) := by
  rcases c with ⟨q, tape⟩
  cases q <;>
    simp [Halted, inputCheckedConfig, inputCheckedEmbed,
      checkedEvalRunLoopMachine, inputNodeCompositeMachine,
      NTM.successors, NTM.stepBranch, List.map_map,
      Function.comp_def, Tape.write, Tape.move] at h ⊢

theorem inputChecked_active
    (mode : SyntaxMode)
    (c : Configuration InputNodeCompositeState (Option Bool))
    (h : ¬ Halted inputNodeCompositeMachine c) :
    ¬ Halted checkedEvalRunLoopMachine (inputCheckedConfig mode c) := by
  rcases c with ⟨q, tape⟩
  cases q <;>
    simp [Halted, inputCheckedConfig, inputCheckedEmbed,
      checkedEvalRunLoopMachine, inputNodeCompositeMachine] at h ⊢

/-- Terminal-aware lift of the indexed-input primitive into the checked loop. -/
theorem input_terminal_reachable_lift :
    ∀ (mode : SyntaxMode) (n : Nat)
      (a b : Configuration InputNodeCompositeState (Option Bool)),
      ¬ Halted inputNodeCompositeMachine a →
      Halted inputNodeCompositeMachine b →
      b ∈ inputNodeCompositeMachine.runBranches n [a] →
      ∃ m ≤ n,
        inputCheckedConfig mode b ∈
          checkedEvalRunLoopMachine.runBranches m
            [inputCheckedConfig mode a] := by
  intro mode n
  induction n with
  | zero =>
      intro a b ha hb hreach
      simp [NTM.runBranches] at hreach
      subst b
      exact False.elim (ha hb)
  | succ n ih =>
      intro a b ha hb hreach
      have hreach' :
          b ∈ inputNodeCompositeMachine.runBranches n
            (inputNodeCompositeMachine.successors a) := by
        change b ∈ inputNodeCompositeMachine.runBranches (n + 1) [a] at hreach
        rw [runBranches_singleton_active
          inputNodeCompositeMachine n a ha] at hreach
        exact hreach
      rw [mem_runBranches_iff] at hreach'
      rcases hreach' with ⟨c, hca, hcb⟩

      have hstepSucc :
          inputCheckedConfig mode c ∈
            checkedEvalRunLoopMachine.successors
              (inputCheckedConfig mode a) := by
        rw [inputChecked_successors_active mode a ha]
        exact List.mem_map.mpr ⟨c, hca, rfl⟩
      have hstep :
          inputCheckedConfig mode c ∈
            checkedEvalRunLoopMachine.runBranches 1
              [inputCheckedConfig mode a] := by
        have h :=
          mem_runBranches_succ_of_successor
            checkedEvalRunLoopMachine 0 [inputCheckedConfig mode a]
            (inputCheckedConfig mode a) (inputCheckedConfig mode c)
            (by simp [NTM.runBranches])
            (inputChecked_active mode a ha) hstepSucc
        simpa using h

      by_cases hc : Halted inputNodeCompositeMachine c
      · have hcb' : b = c := by
          rw [runBranches_singleton_halted
            inputNodeCompositeMachine n c hc] at hcb
          simpa using hcb
        subst b
        exact ⟨1, by omega, hstep⟩
      · obtain ⟨m, hm, htail⟩ := ih c b hc hb hcb
        have htrans :=
          mem_runBranches_trans checkedEvalRunLoopMachine
            1 m [inputCheckedConfig mode a]
            (inputCheckedConfig mode c) (inputCheckedConfig mode b)
            hstep htail
        exact ⟨1 + m, by omega, htrans⟩

/-- Complete indexed-input primitive after the 000 decoder, lifted into the
checked evaluator without changing its physical fuel bound. -/
theorem inputNode_checked_from_read
    (mode : SyntaxMode)
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    ∃ m ≤ inputNodeCompositeFuel consumed i tail frameStack,
      inputCheckedConfig mode
        ({ state :=
             .done (witness.getD i false)
               (inputNodeFinalMode tail frameStack),
           tape :=
             (inputAfterReadTarget witness
               (consumedAfterInputIndex consumed i)
               tail frameStack padding).tape } :
          Configuration InputNodeCompositeState (Option Bool)) ∈
        checkedEvalRunLoopMachine.runBranches m
          [inputCheckedConfig mode
            ({ state := inputNodeCompositeMachine.initial,
               tape :=
                 evalCursorReadTape witness consumed
                   (encodeNat i ++ tail) frameStack padding } :
              Configuration InputNodeCompositeState (Option Bool))] := by
  obtain ⟨m, hm, hsrc⟩ :=
    inputNodeComposite_reaches_done
      witness tail frameStack consumed padding i hi
  let a : Configuration InputNodeCompositeState (Option Bool) :=
    { state := inputNodeCompositeMachine.initial,
      tape :=
        evalCursorReadTape witness consumed
          (encodeNat i ++ tail) frameStack padding }
  let b : Configuration InputNodeCompositeState (Option Bool) :=
    { state :=
        .done (witness.getD i false)
          (inputNodeFinalMode tail frameStack),
      tape :=
        (inputAfterReadTarget witness
          (consumedAfterInputIndex consumed i)
          tail frameStack padding).tape }
  have ha : ¬ Halted inputNodeCompositeMachine a := by
    simp [Halted, a, inputNodeCompositeMachine]
  have hb : Halted inputNodeCompositeMachine b := by
    simp [Halted, b, inputNodeCompositeMachine]
  obtain ⟨k, hk, hlift⟩ :=
    input_terminal_reachable_lift mode m a b ha hb (by
      simpa [a, b] using hsrc)
  exact ⟨k, Nat.le_trans hk hm, by simpa [a, b] using hlift⟩

def checkedInputTagFuel
    (consumed i : Nat) (tail frameStack : BitString) : Nat :=
  checkedTagPrefixFuel
      (false :: false :: false :: (encodeNat i ++ tail)) frameStack +
    inputNodeCompositeFuel (consumed + 3) i tail frameStack

/-- Complete physical 000 route in the checked repeated evaluator. -/
theorem inputTag_checked_reaches_mode
    (mode : SyntaxMode)
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    ∃ m ≤ checkedInputTagFuel consumed i tail frameStack,
      inputCheckedConfig mode
        ({ state :=
             .done (witness.getD i false)
               (inputNodeFinalMode tail frameStack),
           tape :=
             (inputAfterReadTarget witness
               (consumedAfterInputIndex (consumed + 3) i)
               tail frameStack padding).tape } :
          Configuration InputNodeCompositeState (Option Bool)) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: false :: (encodeNat i ++ tail))
                 frameStack padding }] := by
  obtain ⟨m0, hm0, h0⟩ :=
    checked_tag_prefix_reaches
      mode witness (encodeNat i ++ tail) frameStack
      consumed padding false false false (by
        cases mode <;> rfl)

  let tAfter :=
    evalCursorReadTape witness (consumed + 3)
      (encodeNat i ++ tail) frameStack padding
  let cInput0 : Configuration InputNodeCompositeState (Option Bool) :=
    { state := inputNodeCompositeMachine.initial, tape := tAfter }

  have h0' :
      inputCheckedConfig mode cInput0 ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: false :: (encodeNat i ++ tail))
                 frameStack padding }] := by
    simpa [cInput0, tAfter, inputCheckedConfig, postTagState,
      decodeTagBits, childMode] using h0

  obtain ⟨mI, hmI, hI⟩ :=
    inputNode_checked_from_read
      mode witness tail frameStack (consumed + 3) padding i hi

  have hI' :
      inputCheckedConfig mode
        ({ state :=
             .done (witness.getD i false)
               (inputNodeFinalMode tail frameStack),
           tape :=
             (inputAfterReadTarget witness
               (consumedAfterInputIndex (consumed + 3) i)
               tail frameStack padding).tape } :
          Configuration InputNodeCompositeState (Option Bool)) ∈
        checkedEvalRunLoopMachine.runBranches mI
          [inputCheckedConfig mode cInput0] := by
    simpa [cInput0, tAfter] using hI

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 mI
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (false :: false :: false :: (encodeNat i ++ tail))
             frameStack padding }]
      (inputCheckedConfig mode cInput0)
      (inputCheckedConfig mode
        ({ state :=
             .done (witness.getD i false)
               (inputNodeFinalMode tail frameStack),
           tape :=
             (inputAfterReadTarget witness
               (consumedAfterInputIndex (consumed + 3) i)
               tail frameStack padding).tape } :
          Configuration InputNodeCompositeState (Option Bool)))
      h0' hI'

  refine ⟨m0 + mI, ?_, hAll⟩
  dsimp [checkedInputTagFuel] at *
  omega

/-- Input nodes inhabit the checked circuit certificate in every admissible
syntax mode. -/
theorem input_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (i : Nat) :
    CheckedCircuitRunCertificate sigma witness mode (.input i) := by
  intro hmode tail frames consumed padding hlen hread
  have hiVar : i < varBound (.input i) := by
    simp [varBound]
  have hi : i < witness.length :=
    Nat.lt_of_lt_of_le hiVar hlen
  have hvalue : witness.getD i false = sigma i :=
    hread i hiVar

  obtain ⟨m, hm, hrun⟩ :=
    inputTag_checked_reaches_mode
      mode witness tail (encodeEvalFrames frames)
      consumed padding i hi

  let cfg : CheckedConfig :=
    inputCheckedConfig mode
      ({ state :=
           .done (witness.getD i false)
             (inputNodeFinalMode tail (encodeEvalFrames frames)),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex (consumed + 3) i)
             tail (encodeEvalFrames frames) padding).tape } :
        Configuration InputNodeCompositeState (Option Bool))

  refine ⟨m, cfg, ?_, ?_⟩
  · simpa [cfg, encodeCircuit] using hrun
  · change CheckedLoopOutcome witness (exitMode mode (.input i))
      (sigma i) tail frames cfg
    rw [← hvalue]
    cases tail with
    | cons b bs =>
        refine ⟨consumedAfterInputIndex (consumed + 3) i, padding, ?_⟩
        simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
          cfg, inputCheckedConfig, inputCheckedEmbed,
          inputNodeFinalMode, inputAfterReadTarget]
    | nil =>
        cases frames with
        | nil =>
            refine ⟨(inputAfterReadTarget witness
              (consumedAfterInputIndex (consumed + 3) i)
              [] [] padding).tape, ?_⟩
            simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
              cfg, inputCheckedConfig, inputCheckedEmbed,
              inputNodeFinalMode, inputAfterReadTarget]
        | cons f fs =>
            refine ⟨consumedAfterInputIndex (consumed + 3) i, padding, ?_⟩
            cases f with
            | neg =>
                simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, inputCheckedConfig, inputCheckedEmbed,
                  inputNodeFinalMode, inputAfterReadTarget,
                  encodeEvalFrames, encodeEvalFrame]
            | andLeft =>
                simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, inputCheckedConfig, inputCheckedEmbed,
                  inputNodeFinalMode, inputAfterReadTarget,
                  encodeEvalFrames, encodeEvalFrame]
            | andRight b =>
                cases b <;>
                  simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                    cfg, inputCheckedConfig, inputCheckedEmbed,
                    inputNodeFinalMode, inputAfterReadTarget,
                    encodeEvalFrames, encodeEvalFrame]
            | orLeft =>
                simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, inputCheckedConfig, inputCheckedEmbed,
                  inputNodeFinalMode, inputAfterReadTarget,
                  encodeEvalFrames, encodeEvalFrame]
            | orRight b =>
                cases b <;>
                  simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                    cfg, inputCheckedConfig, inputCheckedEmbed,
                    inputNodeFinalMode, inputAfterReadTarget,
                    encodeEvalFrames, encodeEvalFrame]

#print axioms MCore.Real.P01CheckedEvalRunInputTag.inputChecked_successors_active
#print axioms MCore.Real.P01CheckedEvalRunInputTag.input_terminal_reachable_lift
#print axioms MCore.Real.P01CheckedEvalRunInputTag.inputNode_checked_from_read
#print axioms MCore.Real.P01CheckedEvalRunInputTag.inputTag_checked_reaches_mode
#print axioms MCore.Real.P01CheckedEvalRunInputTag.input_certificate

end P01CheckedEvalRunInputTag
end Real
end MCore
