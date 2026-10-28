import Mathlib.Tactic
import MCore.Real.P01CheckedEvalRunBoundedCertificate

namespace MCore
namespace Real
namespace P01ExactBoundedCircuitProducer

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01InputNodeRoundTrip
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunBoundedInput
open P01CheckedEvalRunBoundedConst
open P01CheckedEvalRunBoundedHelpers
open P01CheckedEvalRunBoundedCertificate
open P01CheckedVerifierInvariant
open P01CheckedVerifierGlobalBudget
open P01CNFMode
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Compositional outcome carrying the exact source cursor after one circuit.
The exact cursor is what lets a bounded certificate feed the next child
without losing the layout invariant. -/
def ExactCheckedLoopOutcome
    (witness : BitString)
    (mode : SyntaxMode)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (finalConsumed : Nat)
    (cfg : CheckedConfig) : Prop :=
  match tail, frames with
  | [], [] =>
      ∃ tape : Tape (Option Bool),
        cfg = { state := .final value, tape := tape }
  | _, _ =>
      ∃ padding : Nat,
        cfg =
          { state := .have mode (.start value),
            tape :=
              evalCursorStackEndTape witness finalConsumed tail
                (encodeEvalFrames frames) padding }

/-- Direct bounded producer contract with an exact source cursor.
Unlike a mere existential outcome, this statement is closed under binary
circuit composition. -/
def ExactBoundedCheckedCircuitRunCertificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (phi : CircuitK1.Circuit) : Prop :=
  modeCheck mode phi = true →
  ∀ (tail : BitString) (frames : List EvalFrame)
      (consumed padding n : Nat),
    CheckedLayoutBound n consumed
      (encodeCircuit phi ++ tail) (encodeEvalFrames frames) →
    varBound phi ≤ witness.length →
    (∀ i, i < varBound phi →
      witness.getD i false = sigma i) →
    ∃ m ≤ checkedCircuitBudget phi n, ∃ cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit phi ++ tail)
                 (encodeEvalFrames frames) padding }] ∧
      ExactCheckedLoopOutcome witness (exitMode mode phi)
        (evalCircuit sigma phi) tail frames
        (consumed + (encodeCircuit phi).length) cfg

/-- Static source consumption preserves the global layout budget. -/
theorem layout_consume_prefix
    (n consumed : Nat)
    (bitsPrefix rest frameStack : BitString)
    (h :
      CheckedLayoutBound n consumed
        (bitsPrefix ++ rest) frameStack) :
    CheckedLayoutBound n (consumed + bitsPrefix.length)
      rest frameStack := by
  constructor
  · have hs := h.source_budget
    simp [List.length_append] at hs ⊢
    omega
  · have hf := h.frames_paid
    omega

/-- Every canonical circuit encoding contains a three-bit root tag. -/
theorem encodeCircuit_ne_nil (phi : CircuitK1.Circuit) :
    encodeCircuit phi ≠ [] := by
  cases phi with
  | input i =>
      simp [encodeCircuit]
  | const b =>
      cases b <;> simp [encodeCircuit]
  | not child =>
      simp [encodeCircuit]
  | and left right =>
      simp [encodeCircuit]
  | or left right =>
      simp [encodeCircuit]

/-- Exact bounded leaf producer for input nodes. -/
theorem input_exact_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (i : Nat) :
    ExactBoundedCheckedCircuitRunCertificate
      sigma witness mode (.input i) := by
  intro hmode tail frames consumed padding n hLayout hlen hread
  have hiVar : i < varBound (.input i) := by
    simp [varBound]
  have hi : i < witness.length :=
    Nat.lt_of_lt_of_le hiVar hlen
  have hvalue : witness.getD i false = sigma i :=
    hread i hiVar

  have hLayoutInput :
      CheckedLayoutBound n consumed
        (false :: false :: false :: (encodeNat i ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using hLayout

  obtain ⟨m, hm, hrun⟩ :=
    inputTag_checked_reaches_within_loopEnvelope
      n mode witness tail (encodeEvalFrames frames)
      consumed padding i hi hLayoutInput

  let finalConsumed :=
    consumedAfterInputIndex (consumed + 3) i

  have hfinalConsumed :
      finalConsumed =
        consumed + (encodeCircuit (.input i)).length := by
    unfold finalConsumed consumedAfterInputIndex
    simp [encodeCircuit, P01CheckedVerifierBudget.encodeNat_length]
    omega

  let cfg : CheckedConfig :=
    P01CheckedEvalRunInputTag.inputCheckedConfig mode
      ({ state :=
           .done (witness.getD i false)
             (P01InputNodeCompositeRun.inputNodeFinalMode
               tail (encodeEvalFrames frames)),
         tape :=
           (inputAfterReadTarget witness finalConsumed
             tail (encodeEvalFrames frames) padding).tape } :
        Configuration P01InputNodeCompositeNTM.InputNodeCompositeState
          (Option Bool))

  refine ⟨m,
    Nat.le_trans hm (loopEnvelope_le_checkedCircuitBudget (.input i) n),
    cfg, ?_, ?_⟩
  · simpa [cfg, finalConsumed, encodeCircuit] using hrun
  · change ExactCheckedLoopOutcome witness (exitMode mode (.input i))
      (sigma i) tail frames
      (consumed + (encodeCircuit (.input i)).length) cfg
    rw [← hvalue, ← hfinalConsumed]
    cases tail with
    | cons b bs =>
        refine ⟨padding, ?_⟩
        simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
          cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
          P01CheckedEvalRunLoopNTM.inputCheckedEmbed,
          P01InputNodeCompositeRun.inputNodeFinalMode,
          inputAfterReadTarget]
    | nil =>
        cases frames with
        | nil =>
            refine ⟨(inputAfterReadTarget witness finalConsumed
              [] [] padding).tape, ?_⟩
            simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
              cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
              P01CheckedEvalRunLoopNTM.inputCheckedEmbed,
              P01InputNodeCompositeRun.inputNodeFinalMode,
              inputAfterReadTarget]
        | cons f fs =>
            refine ⟨padding, ?_⟩
            cases f with
            | neg =>
                simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
                  P01CheckedEvalRunLoopNTM.inputCheckedEmbed,
                  P01InputNodeCompositeRun.inputNodeFinalMode,
                  inputAfterReadTarget, encodeEvalFrames, encodeEvalFrame]
            | andLeft =>
                simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
                  P01CheckedEvalRunLoopNTM.inputCheckedEmbed,
                  P01InputNodeCompositeRun.inputNodeFinalMode,
                  inputAfterReadTarget, encodeEvalFrames, encodeEvalFrame]
            | andRight a =>
                cases a <;>
                  simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
                    cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
                    P01CheckedEvalRunLoopNTM.inputCheckedEmbed,
                    P01InputNodeCompositeRun.inputNodeFinalMode,
                    inputAfterReadTarget, encodeEvalFrames, encodeEvalFrame]
            | orLeft =>
                simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
                  P01CheckedEvalRunLoopNTM.inputCheckedEmbed,
                  P01InputNodeCompositeRun.inputNodeFinalMode,
                  inputAfterReadTarget, encodeEvalFrames, encodeEvalFrame]
            | orRight a =>
                cases a <;>
                  simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
                    cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
                    P01CheckedEvalRunLoopNTM.inputCheckedEmbed,
                    P01InputNodeCompositeRun.inputNodeFinalMode,
                    inputAfterReadTarget, encodeEvalFrames, encodeEvalFrame]


/-- Exact bounded leaf producer for constants. -/
theorem const_exact_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (v : Bool) :
    ExactBoundedCheckedCircuitRunCertificate
      sigma witness mode (.const v) := by
  intro hmode tail frames consumed padding n hLayout hlen hread

  obtain ⟨m0, hm0, h0⟩ :=
    const_checked_reaches_have_within_loopEnvelope
      n sigma witness tail frames mode consumed padding v hmode hLayout

  let finalConsumed := consumed + 3
  have hfinalConsumed :
      finalConsumed =
        consumed + (encodeCircuit (.const v)).length := by
    unfold finalConsumed
    cases v <;> simp [encodeCircuit]

  let cHave : CheckedConfig :=
    { state := .have mode (.start v),
      tape :=
        evalCursorStackEndTape witness finalConsumed tail
          (encodeEvalFrames frames) padding }

  have h0' :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.const v) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cHave, finalConsumed] using h0

  have hleafBudget :
      checkedLoopStepEnvelope n ≤
        checkedCircuitBudget (.const v) n := by
    exact loopEnvelope_le_checkedCircuitBudget (.const v) n

  cases tail with
  | cons b bs =>
      refine ⟨m0, Nat.le_trans hm0 hleafBudget, cHave, h0', ?_⟩
      change ExactCheckedLoopOutcome witness (exitMode mode (.const v))
        (evalCircuit sigma (.const v)) (b :: bs) frames
        (consumed + (encodeCircuit (.const v)).length) cHave
      rw [← hfinalConsumed]
      refine ⟨padding, ?_⟩
      cases v <;> cases mode <;>
        simp [ExactCheckedLoopOutcome, exitMode, childMode, circuitTag,
          evalCircuit, cHave, finalConsumed, modeCheck] at hmode ⊢
  | nil =>
      cases frames with
      | cons f fs =>
          refine ⟨m0, Nat.le_trans hm0 hleafBudget, cHave, h0', ?_⟩
          change ExactCheckedLoopOutcome witness (exitMode mode (.const v))
            (evalCircuit sigma (.const v)) [] (f :: fs)
            (consumed + (encodeCircuit (.const v)).length) cHave
          rw [← hfinalConsumed]
          refine ⟨padding, ?_⟩
          cases v <;> cases mode <;>
            simp [ExactCheckedLoopOutcome, exitMode, childMode, circuitTag,
              evalCircuit, cHave, finalConsumed, modeCheck] at hmode ⊢
      | nil =>
          obtain ⟨m1, hm1, cfgFinal, h1, hout1⟩ :=
            have_reaches_outcome_within_envelope
              n mode witness v [] [] finalConsumed padding
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.const v))
                     (encodeEvalFrames []) padding }]
              cHave cfgFinal (by simpa using h0') (by simpa [cHave] using h1)
          have hbudget :
              m0 + m1 ≤ checkedCircuitBudget (.const v) n := by
            have hsum :
                m0 + m1 ≤ 2 * checkedLoopStepEnvelope n := by
              omega
            have h2 :
                2 * checkedLoopStepEnvelope n ≤
                  checkedCircuitBudget (.const v) n := by
              unfold checkedCircuitBudget
              simp [evalStepCount]
              have h :
                  2 ≤ 16 := by omega
              exact Nat.mul_le_mul_right
                (checkedLoopStepEnvelope n) h
            exact Nat.le_trans hsum h2
          refine ⟨m0 + m1, hbudget, cfgFinal, ?_, ?_⟩
          · simpa using hAll
          · change ExactCheckedLoopOutcome witness
              (exitMode mode (.const v))
              (evalCircuit sigma (.const v)) [] []
              (consumed + (encodeCircuit (.const v)).length) cfgFinal
            simp [ExactCheckedLoopOutcome] at hout1 ⊢
            simpa [evalCircuit] using hout1


/-- Exact bounded producer for negation. -/
theorem neg_exact_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (child : CircuitK1.Circuit)
    (hchild :
      ExactBoundedCheckedCircuitRunCertificate
        sigma witness (childMode mode .neg) child) :
    ExactBoundedCheckedCircuitRunCertificate
      sigma witness mode (.not child) := by
  intro hmode tail frames consumed padding n hLayout hlen hread

  have hparts :
      tagAllowed mode .neg = true ∧
        modeCheck (childMode mode .neg) child = true := by
    have h := hmode
    rw [modeCheck_not] at h
    simpa using h
  have hAllowed := hparts.1
  have hchildMode := hparts.2

  have hlenChild : varBound child ≤ witness.length := by
    simpa [varBound] using hlen
  have hreadChild :
      ∀ i, i < varBound child →
        witness.getD i false = sigma i := by
    intro i hi
    exact hread i (by simpa [varBound] using hi)

  have hLayout0 :
      CheckedLayoutBound n consumed
        (false :: true :: true :: (encodeCircuit child ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using hLayout

  have hLayoutChild :
      CheckedLayoutBound n (consumed + 3)
        (encodeCircuit child ++ tail)
        (encodeEvalFrame .neg ++ encodeEvalFrames frames) :=
    after_push_tag n consumed false true true
      (encodeCircuit child ++ tail) (encodeEvalFrames frames) .neg hLayout0

  obtain ⟨m0, hm0, h0⟩ :=
    pushTag_checked_reaches_need_within_envelope
      n mode witness (encodeCircuit child ++ tail)
      (encodeEvalFrames frames) consumed padding
      false true true .neg .neg rfl hAllowed rfl
      hLayout0.source_le hLayout0.frames_le

  let padChild := ((padding - 1) - 1) - 1
  let cNeed : CheckedConfig :=
    { state := .need (childMode mode .neg)
        needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          (encodeCircuit child ++ tail)
          (encodeEvalFrame .neg ++ encodeEvalFrames frames)
          padChild }

  have h0' :
      cNeed ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.not child) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cNeed, padChild, encodeCircuit, List.append_assoc] using h0

  obtain ⟨m1, hm1, cfg1, h1, hout1⟩ :=
    hchild hchildMode tail (.neg :: frames)
      (consumed + 3) padChild n
      (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutChild)
      hlenChild hreadChild

  have h1' :
      cfg1 ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeed] := by
    simpa [cNeed, encodeEvalFrames, List.append_assoc] using h1

  have h01 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 m1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not child) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeed cfg1 h0' h1'

  simp [ExactCheckedLoopOutcome] at hout1
  rcases hout1 with ⟨padding1, hcfg1⟩
  subst cfg1

  let childConsumed :=
    (consumed + 3) + (encodeCircuit child).length

  obtain ⟨m2, hm2, h2⟩ :=
    negReturn_checked_reaches_have_within_envelope
      n (exitMode (childMode mode .neg) child)
      witness tail (encodeEvalFrames frames)
      childConsumed padding1 (evalCircuit sigma child)

  let cHave : CheckedConfig :=
    { state := .have (exitMode (childMode mode .neg) child)
        (.start (!(evalCircuit sigma child))),
      tape :=
        evalCursorStackEndTape witness childConsumed tail
          (encodeEvalFrames frames) (padding1 + 3) }

  have h2' :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches m2
          [{ state := .have (exitMode (childMode mode .neg) child)
               (.start (evalCircuit sigma child)),
             tape :=
               evalCursorStackEndTape witness childConsumed tail
                 (encodeEvalFrame .neg ++ encodeEvalFrames frames)
                 padding1 }] := by
    simpa [cHave, childConsumed] using h2

  have h012 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1) m2
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not child) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have (exitMode (childMode mode .neg) child)
           (.start (evalCircuit sigma child)),
         tape :=
           evalCursorStackEndTape witness childConsumed tail
             (encodeEvalFrame .neg ++ encodeEvalFrames frames)
             padding1 } : CheckedConfig)
      cHave h01 h2'

  have hchildInput :
      ∃ i, child = .input i := by
    have hm : modeCheck .mustInput child = true := by
      simpa [childMode] using hchildMode
    exact (modeCheck_mustInput_iff child).1 hm

  have hExit :
      exitMode (childMode mode .neg) child =
        exitMode mode (.not child) := by
    rcases hchildInput with ⟨i, rfl⟩
    simp [exitMode, childMode, circuitTag]

  have hConsumed :
      childConsumed =
        consumed + (encodeCircuit (.not child)).length := by
    unfold childConsumed
    simp [encodeCircuit]
    omega

  have hprefixBudget :
      m0 + m1 + m2 ≤
        checkedCircuitBudget (.not child) n := by
    have hraw :
        m0 + m1 + m2 ≤
          checkedLoopStepEnvelope n +
            checkedCircuitBudget child n +
            checkedLoopStepEnvelope n := by
      omega
    have hcap :
        checkedLoopStepEnvelope n +
            checkedCircuitBudget child n +
            checkedLoopStepEnvelope n ≤
          checkedCircuitBudget (.not child) n := by
      let E := checkedLoopStepEnvelope n
      have hcoef :
          8 * (evalStepCount child + 1) + 2 ≤
            8 * (evalStepCount child + 3) := by omega
      have hmul :=
        Nat.mul_le_mul_right E hcoef
      have hcount :
          evalStepCount (.not child) + 1 =
            evalStepCount child + 3 := by
        simp [evalStepCount]
        omega
      calc
        checkedLoopStepEnvelope n +
              checkedCircuitBudget child n +
              checkedLoopStepEnvelope n
            = checkedCircuitBudget child n + 2 * E := by
                dsimp [E]
                omega
        _ = (8 * (evalStepCount child + 1) + 2) * E := by
              unfold checkedCircuitBudget
              rw [Nat.add_mul]
        _ ≤ (8 * (evalStepCount child + 3)) * E := hmul
        _ = checkedCircuitBudget (.not child) n := by
              unfold checkedCircuitBudget
              rw [hcount]
    exact Nat.le_trans hraw hcap

  cases tail with
  | cons b bs =>
      refine ⟨m0 + m1 + m2, hprefixBudget, cHave, h012, ?_⟩
      change ExactCheckedLoopOutcome witness (exitMode mode (.not child))
        (evalCircuit sigma (.not child)) (b :: bs) frames
        (consumed + (encodeCircuit (.not child)).length) cHave
      rw [← hConsumed, ← hExit]
      refine ⟨padding1 + 3, ?_⟩
      simp [ExactCheckedLoopOutcome, cHave, childConsumed, evalCircuit]
  | nil =>
      cases frames with
      | cons f fs =>
          refine ⟨m0 + m1 + m2, hprefixBudget, cHave, h012, ?_⟩
          change ExactCheckedLoopOutcome witness (exitMode mode (.not child))
            (evalCircuit sigma (.not child)) [] (f :: fs)
            (consumed + (encodeCircuit (.not child)).length) cHave
          rw [← hConsumed, ← hExit]
          refine ⟨padding1 + 3, ?_⟩
          simp [ExactCheckedLoopOutcome, cHave, childConsumed, evalCircuit]
      | nil =>
          obtain ⟨m3, hm3, cfgFinal, h3, hout3⟩ :=
            have_reaches_outcome_within_envelope
              n (exitMode (childMode mode .neg) child)
              witness (!(evalCircuit sigma child))
              [] [] childConsumed (padding1 + 3)
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1 + m2) m3
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.not child))
                     (encodeEvalFrames []) padding }]
              cHave cfgFinal (by simpa using h012)
              (by simpa [cHave] using h3)
          have hfinalBudget :
              m0 + m1 + m2 + m3 ≤
                checkedCircuitBudget (.not child) n := by
            have hraw :
                m0 + m1 + m2 + m3 ≤
                  checkedLoopStepEnvelope n +
                    checkedCircuitBudget child n +
                    checkedLoopStepEnvelope n +
                    checkedLoopStepEnvelope n := by
              omega
            have hcap :
                checkedLoopStepEnvelope n +
                    checkedCircuitBudget child n +
                    checkedLoopStepEnvelope n +
                    checkedLoopStepEnvelope n ≤
                  checkedCircuitBudget (.not child) n := by
              let E := checkedLoopStepEnvelope n
              have hcoef :
                  8 * (evalStepCount child + 1) + 3 ≤
                    8 * (evalStepCount child + 3) := by omega
              have hmul := Nat.mul_le_mul_right E hcoef
              have hcount :
                  evalStepCount (.not child) + 1 =
                    evalStepCount child + 3 := by
                simp [evalStepCount]
                omega
              calc
                checkedLoopStepEnvelope n +
                      checkedCircuitBudget child n +
                      checkedLoopStepEnvelope n +
                      checkedLoopStepEnvelope n
                    = checkedCircuitBudget child n + 3 * E := by
                        dsimp [E]
                        omega
                _ = (8 * (evalStepCount child + 1) + 3) * E := by
                      unfold checkedCircuitBudget
                      rw [Nat.add_mul]
                _ ≤ (8 * (evalStepCount child + 3)) * E := hmul
                _ = checkedCircuitBudget (.not child) n := by
                      unfold checkedCircuitBudget
                      rw [hcount]
            exact Nat.le_trans hraw hcap
          refine ⟨m0 + m1 + m2 + m3, hfinalBudget, cfgFinal, ?_, ?_⟩
          · simpa using hAll
          · change ExactCheckedLoopOutcome witness (exitMode mode (.not child))
              (evalCircuit sigma (.not child)) [] []
              (consumed + (encodeCircuit (.not child)).length) cfgFinal
            simp [ExactCheckedLoopOutcome] at hout3 ⊢
            simpa [evalCircuit] using hout3



/-- Exact outcome with nonempty unread source is necessarily a have-state at
the statically known source cursor. -/
theorem exact_outcome_have_of_tail_ne_nil
    (witness : BitString)
    (mode : SyntaxMode)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (finalConsumed : Nat)
    (cfg : CheckedConfig)
    (hne : tail ≠ [])
    (h :
      ExactCheckedLoopOutcome witness mode value tail frames
        finalConsumed cfg) :
    ∃ padding,
      cfg =
        { state := .have mode (.start value),
          tape :=
            evalCursorStackEndTape witness finalConsumed tail
              (encodeEvalFrames frames) padding } := by
  cases tail with
  | nil => exact False.elim (hne rfl)
  | cons b bs => exact h

/-- Exact outcome with a nonempty continuation stack is necessarily a
have-state at the statically known source cursor. -/
theorem exact_outcome_have_of_frames_ne_nil
    (witness : BitString)
    (mode : SyntaxMode)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (finalConsumed : Nat)
    (cfg : CheckedConfig)
    (hne : frames ≠ [])
    (h :
      ExactCheckedLoopOutcome witness mode value tail frames
        finalConsumed cfg) :
    ∃ padding,
      cfg =
        { state := .have mode (.start value),
          tape :=
            evalCursorStackEndTape witness finalConsumed tail
              (encodeEvalFrames frames) padding } := by
  cases tail with
  | cons b bs => exact h
  | nil =>
      cases frames with
      | nil => exact False.elim (hne rfl)
      | cons f fs => exact h

/-- The static layout budget after consuming a bitsPrefix and replacing the
top continuation frame by another three-bit frame. -/
theorem layout_after_prefix_with_frame
    (n consumed : Nat)
    (bitsPrefix rest frameStack : BitString)
    (frame : EvalFrame)
    (hprefix : 3 ≤ bitsPrefix.length)
    (h :
      CheckedLayoutBound n consumed
        (bitsPrefix ++ rest) frameStack) :
    CheckedLayoutBound n (consumed + bitsPrefix.length)
      rest (encodeEvalFrame frame ++ frameStack) := by
  have hp := layout_consume_prefix n consumed bitsPrefix rest frameStack h
  constructor
  · exact hp.source_budget
  · rw [List.length_append, encodeEvalFrame_length]
    have hf := h.frames_paid
    omega

/-- Exact bounded producer for conjunction.  This is the missing binary
composition: tag, exact left child, left-frame handoff, exact right child,
right-frame handoff, and (only when needed) final normalization. -/
theorem and_exact_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (left right : CircuitK1.Circuit)
    (hleft :
      ExactBoundedCheckedCircuitRunCertificate
        sigma witness .cnf left)
    (hright :
      ExactBoundedCheckedCircuitRunCertificate
        sigma witness .cnf right) :
    ExactBoundedCheckedCircuitRunCertificate
      sigma witness mode (.and left right) := by
  intro hmode tail frames consumed padding n hLayout hlen hread

  cases mode with
  | clause =>
      rw [modeCheck_and] at hmode
      simp [tagAllowed] at hmode
  | mustInput =>
      rw [modeCheck_and] at hmode
      simp [tagAllowed] at hmode
  | cnf =>
      have hchildren :
          modeCheck .cnf left = true ∧
            modeCheck .cnf right = true := by
        have h := hmode
        rw [modeCheck_and] at h
        simpa [tagAllowed] using h
      have hleftMode := hchildren.1
      have hrightMode := hchildren.2

      have hlenMax :
          max (varBound left) (varBound right) ≤ witness.length := by
        simpa [varBound] using hlen
      have hlenLeft : varBound left ≤ witness.length :=
        Nat.le_trans (Nat.le_max_left _ _) hlenMax
      have hlenRight : varBound right ≤ witness.length :=
        Nat.le_trans (Nat.le_max_right _ _) hlenMax
      have hreadLeft :
          ∀ i, i < varBound left →
            witness.getD i false = sigma i := by
        intro j hj
        exact hread j (by
          simpa [varBound] using
            Nat.lt_of_lt_of_le hj (Nat.le_max_left _ _))
      have hreadRight :
          ∀ i, i < varBound right →
            witness.getD i false = sigma i := by
        intro j hj
        exact hread j (by
          simpa [varBound] using
            Nat.lt_of_lt_of_le hj (Nat.le_max_right _ _))

      have hLayout0 :
          CheckedLayoutBound n consumed
            (true :: false :: false ::
              (encodeCircuit left ++ encodeCircuit right ++ tail))
            (encodeEvalFrames frames) := by
        simpa [encodeCircuit, List.append_assoc] using hLayout

      obtain ⟨m0, hm0, h0⟩ :=
        pushTag_checked_reaches_need_within_envelope
          n .cnf witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false false .and .andLeft rfl rfl (by
            simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
          hLayout0.source_le hLayout0.frames_le

      let padLeft := ((padding - 1) - 1) - 1
      let leftConsumed := consumed + 3
      let cNeedLeft : CheckedConfig :=
        { state := .need .cnf needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness leftConsumed
              (encodeCircuit left ++ encodeCircuit right ++ tail)
              (encodeEvalFrame .andLeft ++ encodeEvalFrames frames)
              padLeft }

      have h0' :
          cNeedLeft ∈
            checkedEvalRunLoopMachine.runBranches m0
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.and left right) ++ tail)
                     (encodeEvalFrames frames) padding }] := by
        simpa [cNeedLeft, leftConsumed, padLeft, encodeCircuit,
          List.append_assoc] using h0

      have hLayoutLeft :
          CheckedLayoutBound n leftConsumed
            (encodeCircuit left ++ (encodeCircuit right ++ tail))
            (encodeEvalFrame .andLeft ++ encodeEvalFrames frames) := by
        simpa [leftConsumed, List.append_assoc] using
          (after_push_tag n consumed true false false
            (encodeCircuit left ++ encodeCircuit right ++ tail)
            (encodeEvalFrames frames) .andLeft hLayout0)

      obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
        hleft hleftMode
          (encodeCircuit right ++ tail) (.andLeft :: frames)
          leftConsumed padLeft n
          (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
          hlenLeft hreadLeft

      have h1' :
          cfgLeft ∈
            checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
        simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1

      have h01 :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          m0 m1
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.and left right) ++ tail)
                 (encodeEvalFrames frames) padding }]
          cNeedLeft cfgLeft h0' h1'

      let afterLeft :=
        leftConsumed + (encodeCircuit left).length

      have hRightTail : encodeCircuit right ++ tail ≠ [] := by
        intro hnil
        have henc : encodeCircuit right = [] :=
          (List.append_eq_nil_iff.mp hnil).1
        exact encodeCircuit_ne_nil right henc

      obtain ⟨padding1, hcfgLeft⟩ :=
        exact_outcome_have_of_tail_ne_nil
          witness (exitMode .cnf left) (evalCircuit sigma left)
          (encodeCircuit right ++ tail) (.andLeft :: frames)
          afterLeft cfgLeft hRightTail
          (by simpa [afterLeft] using hout1)
      subst cfgLeft

      obtain ⟨m2, hm2, h2⟩ :=
        andLeftReturn_checked_reaches_need_within_envelope
          n (exitMode .cnf left)
          witness (encodeCircuit right ++ tail)
          (encodeEvalFrames frames)
          afterLeft padding1 (evalCircuit sigma left)

      let padRight := (((padding1 + 3) - 1) - 1) - 1
      let cNeedRight : CheckedConfig :=
        { state := .need .cnf needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness afterLeft
              (encodeCircuit right ++ tail)
              (encodeEvalFrame (.andRight (evalCircuit sigma left)) ++
                encodeEvalFrames frames)
              padRight }

      have h2' :
          cNeedRight ∈
            checkedEvalRunLoopMachine.runBranches m2
              [{ state := .have (exitMode .cnf left)
                   (.start (evalCircuit sigma left)),
                 tape :=
                   evalCursorStackEndTape witness afterLeft
                     (encodeCircuit right ++ tail)
                     (encodeEvalFrames (.andLeft :: frames))
                     padding1 }] := by
        simpa [cNeedRight, padRight, encodeEvalFrames,
          List.append_assoc] using h2

      have h012 :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          (m0 + m1) m2
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.and left right) ++ tail)
                 (encodeEvalFrames frames) padding }]
          ({ state := .have (exitMode .cnf left)
               (.start (evalCircuit sigma left)),
             tape :=
               evalCursorStackEndTape witness afterLeft
                 (encodeCircuit right ++ tail)
                 (encodeEvalFrames (.andLeft :: frames))
                 padding1 } : CheckedConfig)
          cNeedRight h01 h2'

      have hLayoutRight :
          CheckedLayoutBound n afterLeft
            (encodeCircuit right ++ tail)
            (encodeEvalFrame (.andRight (evalCircuit sigma left)) ++
              encodeEvalFrames frames) := by
        have hp :
            CheckedLayoutBound n
              (consumed +
                (true :: false :: false :: encodeCircuit left).length)
              (encodeCircuit right ++ tail)
              (encodeEvalFrame (.andRight (evalCircuit sigma left)) ++
                encodeEvalFrames frames) := by
          apply layout_after_prefix_with_frame
            n consumed
            (true :: false :: false :: encodeCircuit left)
            (encodeCircuit right ++ tail)
            (encodeEvalFrames frames)
            (.andRight (evalCircuit sigma left))
            (by simp)
          simpa [encodeCircuit, List.append_assoc] using hLayout
        convert hp using 1 <;> simp [afterLeft, leftConsumed] <;> omega

      obtain ⟨m3, hm3, cfgRight, h3, hout3⟩ :=
        hright hrightMode tail
          (.andRight (evalCircuit sigma left) :: frames)
          afterLeft padRight n
          (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutRight)
          hlenRight hreadRight

      have h3' :
          cfgRight ∈
            checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
        simpa [cNeedRight, encodeEvalFrames, List.append_assoc] using h3

      have h0123 :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          (m0 + m1 + m2) m3
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.and left right) ++ tail)
                 (encodeEvalFrames frames) padding }]
          cNeedRight cfgRight h012 h3'

      let finalConsumed :=
        afterLeft + (encodeCircuit right).length

      obtain ⟨padding2, hcfgRight⟩ :=
        exact_outcome_have_of_frames_ne_nil
          witness (exitMode .cnf right) (evalCircuit sigma right)
          tail (.andRight (evalCircuit sigma left) :: frames)
          finalConsumed cfgRight (by simp)
          (by simpa [finalConsumed] using hout3)
      subst cfgRight

      obtain ⟨m4, hm4, h4⟩ :=
        andRightReturn_checked_reaches_have_within_envelope
          n (exitMode .cnf right)
          witness tail (encodeEvalFrames frames)
          finalConsumed padding2
          (evalCircuit sigma left) (evalCircuit sigma right)

      let finalValue :=
        Bool.and (evalCircuit sigma left) (evalCircuit sigma right)
      let cHave : CheckedConfig :=
        { state := .have .cnf (.start finalValue),
          tape :=
            evalCursorStackEndTape witness finalConsumed tail
              (encodeEvalFrames frames) (padding2 + 3) }

      have h4' :
          cHave ∈
            checkedEvalRunLoopMachine.runBranches m4
              [{ state := .have (exitMode .cnf right)
                   (.start (evalCircuit sigma right)),
                 tape :=
                   evalCursorStackEndTape witness finalConsumed tail
                     (encodeEvalFrames
                       (.andRight (evalCircuit sigma left) :: frames))
                     padding2 }] := by
        simpa [cHave, finalValue, encodeEvalFrames,
          List.append_assoc] using h4

      have h01234 :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          (m0 + m1 + m2 + m3) m4
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.and left right) ++ tail)
                 (encodeEvalFrames frames) padding }]
          ({ state := .have (exitMode .cnf right)
               (.start (evalCircuit sigma right)),
             tape :=
               evalCursorStackEndTape witness finalConsumed tail
                 (encodeEvalFrames
                   (.andRight (evalCircuit sigma left) :: frames))
                 padding2 } : CheckedConfig)
          cHave h0123 h4'

      have hConsumed :
          finalConsumed =
            consumed + (encodeCircuit (.and left right)).length := by
        unfold finalConsumed afterLeft leftConsumed
        simp [encodeCircuit]
        omega

      have hPrefixBudget :
          m0 + m1 + m2 + m3 + m4 ≤
            checkedCircuitBudget (.and left right) n := by
        have hraw :
            m0 + m1 + m2 + m3 + m4 ≤
              checkedLoopStepEnvelope n +
                checkedCircuitBudget left n +
                checkedLoopStepEnvelope n +
                checkedCircuitBudget right n +
                checkedLoopStepEnvelope n := by
          omega
        let E := checkedLoopStepEnvelope n
        have hcoef :
            8 * (evalStepCount left + 1) +
                8 * (evalStepCount right + 1) + 3 ≤
              8 * (evalStepCount left + evalStepCount right + 4) := by
          omega
        have hmul :=
          Nat.mul_le_mul_right E hcoef
        have hcount :
            evalStepCount (.and left right) + 1 =
              evalStepCount left + evalStepCount right + 4 := by
          simp [evalStepCount]
          omega
        have hcap :
            checkedLoopStepEnvelope n +
                checkedCircuitBudget left n +
                checkedLoopStepEnvelope n +
                checkedCircuitBudget right n +
                checkedLoopStepEnvelope n ≤
              checkedCircuitBudget (.and left right) n := by
          calc
            checkedLoopStepEnvelope n +
                  checkedCircuitBudget left n +
                  checkedLoopStepEnvelope n +
                  checkedCircuitBudget right n +
                  checkedLoopStepEnvelope n
                =
              (8 * (evalStepCount left + 1) +
                8 * (evalStepCount right + 1) + 3) * E := by
                  unfold checkedCircuitBudget
                  dsimp [E]
                  ring
            _ ≤
              8 * (evalStepCount left + evalStepCount right + 4) * E :=
                hmul
            _ = checkedCircuitBudget (.and left right) n := by
                  unfold checkedCircuitBudget
                  rw [hcount]
        exact Nat.le_trans hraw hcap

      cases tail with
      | cons b bs =>
          refine ⟨m0 + m1 + m2 + m3 + m4,
            hPrefixBudget, cHave, h01234, ?_⟩
          change ExactCheckedLoopOutcome witness
            (exitMode .cnf (.and left right))
            (evalCircuit sigma (.and left right))
            (b :: bs) frames
            (consumed + (encodeCircuit (.and left right)).length) cHave
          rw [← hConsumed]
          refine ⟨padding2 + 3, ?_⟩
          simp [ExactCheckedLoopOutcome, exitMode, childMode, circuitTag,
            cHave, finalValue, evalCircuit]
      | nil =>
          cases frames with
          | cons f fs =>
              refine ⟨m0 + m1 + m2 + m3 + m4,
                hPrefixBudget, cHave, h01234, ?_⟩
              change ExactCheckedLoopOutcome witness
                (exitMode .cnf (.and left right))
                (evalCircuit sigma (.and left right))
                [] (f :: fs)
                (consumed + (encodeCircuit (.and left right)).length) cHave
              rw [← hConsumed]
              refine ⟨padding2 + 3, ?_⟩
              simp [ExactCheckedLoopOutcome, exitMode, childMode, circuitTag,
                cHave, finalValue, evalCircuit]
          | nil =>
              obtain ⟨m5, hm5, cfgFinal, h5, hout5⟩ :=
                have_reaches_outcome_within_envelope
                  n .cnf witness finalValue [] []
                  finalConsumed (padding2 + 3)
              have hAll :=
                mem_runBranches_trans checkedEvalRunLoopMachine
                  (m0 + m1 + m2 + m3 + m4) m5
                  [{ state := .need .cnf needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness consumed
                         (encodeCircuit (.and left right))
                         (encodeEvalFrames []) padding }]
                  cHave cfgFinal (by simpa using h01234)
                  (by simpa [cHave] using h5)
              have hFinalBudget :
                  m0 + m1 + m2 + m3 + m4 + m5 ≤
                    checkedCircuitBudget (.and left right) n := by
                have hraw :
                    m0 + m1 + m2 + m3 + m4 + m5 ≤
                      checkedLoopStepEnvelope n +
                        checkedCircuitBudget left n +
                        checkedLoopStepEnvelope n +
                        checkedCircuitBudget right n +
                        checkedLoopStepEnvelope n +
                        checkedLoopStepEnvelope n := by
                  omega
                let E := checkedLoopStepEnvelope n
                have hcoef :
                    8 * (evalStepCount left + 1) +
                        8 * (evalStepCount right + 1) + 4 ≤
                      8 * (evalStepCount left + evalStepCount right + 4) := by
                  omega
                have hmul := Nat.mul_le_mul_right E hcoef
                have hcount :
                    evalStepCount (.and left right) + 1 =
                      evalStepCount left + evalStepCount right + 4 := by
                  simp [evalStepCount]
                  omega
                have hcap :
                    checkedLoopStepEnvelope n +
                        checkedCircuitBudget left n +
                        checkedLoopStepEnvelope n +
                        checkedCircuitBudget right n +
                        checkedLoopStepEnvelope n +
                        checkedLoopStepEnvelope n ≤
                      checkedCircuitBudget (.and left right) n := by
                  calc
                    checkedLoopStepEnvelope n +
                          checkedCircuitBudget left n +
                          checkedLoopStepEnvelope n +
                          checkedCircuitBudget right n +
                          checkedLoopStepEnvelope n +
                          checkedLoopStepEnvelope n
                        =
                      (8 * (evalStepCount left + 1) +
                        8 * (evalStepCount right + 1) + 4) * E := by
                          unfold checkedCircuitBudget
                          dsimp [E]
                          ring
                    _ ≤
                      8 * (evalStepCount left + evalStepCount right + 4) * E :=
                        hmul
                    _ = checkedCircuitBudget (.and left right) n := by
                          unfold checkedCircuitBudget
                          rw [hcount]
                exact Nat.le_trans hraw hcap
              refine ⟨m0 + m1 + m2 + m3 + m4 + m5,
                hFinalBudget, cfgFinal, ?_, ?_⟩
              · simpa using hAll
              · change ExactCheckedLoopOutcome witness
                  (exitMode .cnf (.and left right))
                  (evalCircuit sigma (.and left right)) [] []
                  (consumed + (encodeCircuit (.and left right)).length)
                  cfgFinal
                simp [ExactCheckedLoopOutcome] at hout5 ⊢
                simpa [exitMode, childMode, circuitTag, finalValue,
                  evalCircuit] using hout5


theorem or_exact_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (left right : CircuitK1.Circuit)
    (hleft :
      ExactBoundedCheckedCircuitRunCertificate
        sigma witness .clause left)
    (hright :
      ExactBoundedCheckedCircuitRunCertificate
        sigma witness .clause right) :
    ExactBoundedCheckedCircuitRunCertificate
      sigma witness mode (.or left right) := by
  intro hmode tail frames consumed padding n hLayout hlen hread

  have hparts :
      (tagAllowed mode .or = true ∧ modeCheck .clause left = true) ∧
        modeCheck .clause right = true := by
    have h := hmode
    rw [modeCheck_or] at h
    simpa using h
  have hAllowed : tagAllowed mode .or = true := hparts.1.1
  have hleftMode : modeCheck .clause left = true := hparts.1.2
  have hrightMode : modeCheck .clause right = true := hparts.2

  have hlenMax :
      max (varBound left) (varBound right) ≤ witness.length := by
    simpa [varBound] using hlen
  have hlenLeft : varBound left ≤ witness.length :=
    Nat.le_trans (Nat.le_max_left _ _) hlenMax
  have hlenRight : varBound right ≤ witness.length :=
    Nat.le_trans (Nat.le_max_right _ _) hlenMax
  have hreadLeft :
      ∀ i, i < varBound left →
        witness.getD i false = sigma i := by
    intro j hj
    exact hread j (by
      simpa [varBound] using
        Nat.lt_of_lt_of_le hj (Nat.le_max_left _ _))
  have hreadRight :
      ∀ i, i < varBound right →
        witness.getD i false = sigma i := by
    intro j hj
    exact hread j (by
      simpa [varBound] using
        Nat.lt_of_lt_of_le hj (Nat.le_max_right _ _))

  have hLayout0 :
      CheckedLayoutBound n consumed
        (true :: false :: true ::
          (encodeCircuit left ++ encodeCircuit right ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using hLayout

  obtain ⟨m0, hm0, h0⟩ :=
    pushTag_checked_reaches_need_within_envelope
      n mode witness
      (encodeCircuit left ++ encodeCircuit right ++ tail)
      (encodeEvalFrames frames) consumed padding
      true false true .or .orLeft rfl hAllowed (by
        simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
      hLayout0.source_le hLayout0.frames_le

  let padLeft := ((padding - 1) - 1) - 1
  let leftConsumed := consumed + 3
  let cNeedLeft : CheckedConfig :=
    { state := .need .clause needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness leftConsumed
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrame .orLeft ++ encodeEvalFrames frames)
          padLeft }

  have h0' :
      cNeedLeft ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.or left right) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cNeedLeft, leftConsumed, padLeft, encodeCircuit,
      childMode, List.append_assoc] using h0

  have hLayoutLeft :
      CheckedLayoutBound n leftConsumed
        (encodeCircuit left ++ (encodeCircuit right ++ tail))
        (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) := by
    simpa [leftConsumed, List.append_assoc] using
      (after_push_tag n consumed true false true
        (encodeCircuit left ++ encodeCircuit right ++ tail)
        (encodeEvalFrames frames) .orLeft hLayout0)

  obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
    hleft hleftMode
      (encodeCircuit right ++ tail) (.orLeft :: frames)
      leftConsumed padLeft n
      (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
      hlenLeft hreadLeft

  have h1' :
      cfgLeft ∈
        checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
    simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1

  have h01 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 m1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeedLeft cfgLeft h0' h1'

  let afterLeft :=
    leftConsumed + (encodeCircuit left).length

  have hRightTail : encodeCircuit right ++ tail ≠ [] := by
    intro hnil
    have henc : encodeCircuit right = [] :=
      (List.append_eq_nil_iff.mp hnil).1
    exact encodeCircuit_ne_nil right henc

  obtain ⟨padding1, hcfgLeft⟩ :=
    exact_outcome_have_of_tail_ne_nil
      witness (exitMode .clause left) (evalCircuit sigma left)
      (encodeCircuit right ++ tail) (.orLeft :: frames)
      afterLeft cfgLeft hRightTail
      (by simpa [afterLeft] using hout1)
  subst cfgLeft

  obtain ⟨m2, hm2, h2⟩ :=
    orLeftReturn_checked_reaches_need_within_envelope
      n (exitMode .clause left)
      witness (encodeCircuit right ++ tail)
      (encodeEvalFrames frames)
      afterLeft padding1 (evalCircuit sigma left)

  let padRight := (((padding1 + 3) - 1) - 1) - 1
  let cNeedRight : CheckedConfig :=
    { state := .need .clause needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness afterLeft
          (encodeCircuit right ++ tail)
          (encodeEvalFrame (.orRight (evalCircuit sigma left)) ++
            encodeEvalFrames frames)
          padRight }

  have h2' :
      cNeedRight ∈
        checkedEvalRunLoopMachine.runBranches m2
          [{ state := .have (exitMode .clause left)
               (.start (evalCircuit sigma left)),
             tape :=
               evalCursorStackEndTape witness afterLeft
                 (encodeCircuit right ++ tail)
                 (encodeEvalFrames (.orLeft :: frames))
                 padding1 }] := by
    simpa [cNeedRight, padRight, encodeEvalFrames,
      List.append_assoc] using h2

  have h012 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1) m2
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have (exitMode .clause left)
           (.start (evalCircuit sigma left)),
         tape :=
           evalCursorStackEndTape witness afterLeft
             (encodeCircuit right ++ tail)
             (encodeEvalFrames (.orLeft :: frames))
             padding1 } : CheckedConfig)
      cNeedRight h01 h2'

  have hLayoutRight :
      CheckedLayoutBound n afterLeft
        (encodeCircuit right ++ tail)
        (encodeEvalFrame (.orRight (evalCircuit sigma left)) ++
          encodeEvalFrames frames) := by
    have hp :
        CheckedLayoutBound n
          (consumed +
            (true :: false :: true :: encodeCircuit left).length)
          (encodeCircuit right ++ tail)
          (encodeEvalFrame (.orRight (evalCircuit sigma left)) ++
            encodeEvalFrames frames) := by
      apply layout_after_prefix_with_frame
        n consumed
        (true :: false :: true :: encodeCircuit left)
        (encodeCircuit right ++ tail)
        (encodeEvalFrames frames)
        (.orRight (evalCircuit sigma left))
        (by simp)
      simpa [encodeCircuit, List.append_assoc] using hLayout
    convert hp using 1 <;> simp [afterLeft, leftConsumed] <;> omega

  obtain ⟨m3, hm3, cfgRight, h3, hout3⟩ :=
    hright hrightMode tail
      (.orRight (evalCircuit sigma left) :: frames)
      afterLeft padRight n
      (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutRight)
      hlenRight hreadRight

  have h3' :
      cfgRight ∈
        checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
    simpa [cNeedRight, encodeEvalFrames, List.append_assoc] using h3

  have h0123 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1 + m2) m3
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeedRight cfgRight h012 h3'

  let finalConsumed :=
    afterLeft + (encodeCircuit right).length

  obtain ⟨padding2, hcfgRight⟩ :=
    exact_outcome_have_of_frames_ne_nil
      witness (exitMode .clause right) (evalCircuit sigma right)
      tail (.orRight (evalCircuit sigma left) :: frames)
      finalConsumed cfgRight (by simp)
      (by simpa [finalConsumed] using hout3)
  subst cfgRight

  obtain ⟨m4, hm4, h4⟩ :=
    orRightReturn_checked_reaches_have_within_envelope
      n (exitMode .clause right)
      witness tail (encodeEvalFrames frames)
      finalConsumed padding2
      (evalCircuit sigma left) (evalCircuit sigma right)

  let finalValue :=
    Bool.or (evalCircuit sigma left) (evalCircuit sigma right)
  let cHave : CheckedConfig :=
    { state := .have .clause (.start finalValue),
      tape :=
        evalCursorStackEndTape witness finalConsumed tail
          (encodeEvalFrames frames) (padding2 + 3) }

  have h4' :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches m4
          [{ state := .have (exitMode .clause right)
               (.start (evalCircuit sigma right)),
             tape :=
               evalCursorStackEndTape witness finalConsumed tail
                 (encodeEvalFrames
                   (.orRight (evalCircuit sigma left) :: frames))
                 padding2 }] := by
    simpa [cHave, finalValue, encodeEvalFrames,
      List.append_assoc] using h4

  have h01234 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1 + m2 + m3) m4
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have (exitMode .clause right)
           (.start (evalCircuit sigma right)),
         tape :=
           evalCursorStackEndTape witness finalConsumed tail
             (encodeEvalFrames
               (.orRight (evalCircuit sigma left) :: frames))
             padding2 } : CheckedConfig)
      cHave h0123 h4'

  have hConsumed :
      finalConsumed =
        consumed + (encodeCircuit (.or left right)).length := by
    unfold finalConsumed afterLeft leftConsumed
    simp [encodeCircuit]
    omega

  have hPrefixBudget :
      m0 + m1 + m2 + m3 + m4 ≤
        checkedCircuitBudget (.or left right) n := by
    have hraw :
        m0 + m1 + m2 + m3 + m4 ≤
          checkedLoopStepEnvelope n +
            checkedCircuitBudget left n +
            checkedLoopStepEnvelope n +
            checkedCircuitBudget right n +
            checkedLoopStepEnvelope n := by
      omega
    let E := checkedLoopStepEnvelope n
    have hcoef :
        8 * (evalStepCount left + 1) +
            8 * (evalStepCount right + 1) + 3 ≤
          8 * (evalStepCount left + evalStepCount right + 4) := by
      omega
    have hmul :=
      Nat.mul_le_mul_right E hcoef
    have hcount :
        evalStepCount (.or left right) + 1 =
          evalStepCount left + evalStepCount right + 4 := by
      simp [evalStepCount]
      omega
    have hcap :
        checkedLoopStepEnvelope n +
            checkedCircuitBudget left n +
            checkedLoopStepEnvelope n +
            checkedCircuitBudget right n +
            checkedLoopStepEnvelope n ≤
          checkedCircuitBudget (.or left right) n := by
      calc
        checkedLoopStepEnvelope n +
              checkedCircuitBudget left n +
              checkedLoopStepEnvelope n +
              checkedCircuitBudget right n +
              checkedLoopStepEnvelope n
            =
          (8 * (evalStepCount left + 1) +
            8 * (evalStepCount right + 1) + 3) * E := by
              unfold checkedCircuitBudget
              dsimp [E]
              ring
        _ ≤
          8 * (evalStepCount left + evalStepCount right + 4) * E :=
            hmul
        _ = checkedCircuitBudget (.or left right) n := by
              unfold checkedCircuitBudget
              rw [hcount]
    exact Nat.le_trans hraw hcap

  cases tail with
  | cons b bs =>
      refine ⟨m0 + m1 + m2 + m3 + m4,
        hPrefixBudget, cHave, h01234, ?_⟩
      change ExactCheckedLoopOutcome witness
        (exitMode mode (.or left right))
        (evalCircuit sigma (.or left right))
        (b :: bs) frames
        (consumed + (encodeCircuit (.or left right)).length) cHave
      rw [← hConsumed]
      refine ⟨padding2 + 3, ?_⟩
      simp [ExactCheckedLoopOutcome, exitMode, childMode, circuitTag,
        cHave, finalValue, evalCircuit]
  | nil =>
      cases frames with
      | cons f fs =>
          refine ⟨m0 + m1 + m2 + m3 + m4,
            hPrefixBudget, cHave, h01234, ?_⟩
          change ExactCheckedLoopOutcome witness
            (exitMode mode (.or left right))
            (evalCircuit sigma (.or left right))
            [] (f :: fs)
            (consumed + (encodeCircuit (.or left right)).length) cHave
          rw [← hConsumed]
          refine ⟨padding2 + 3, ?_⟩
          simp [ExactCheckedLoopOutcome, exitMode, childMode, circuitTag,
            cHave, finalValue, evalCircuit]
      | nil =>
          obtain ⟨m5, hm5, cfgFinal, h5, hout5⟩ :=
            have_reaches_outcome_within_envelope
              n .clause witness finalValue [] []
              finalConsumed (padding2 + 3)
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1 + m2 + m3 + m4) m5
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.or left right))
                     (encodeEvalFrames []) padding }]
              cHave cfgFinal (by simpa using h01234)
              (by simpa [cHave] using h5)
          have hFinalBudget :
              m0 + m1 + m2 + m3 + m4 + m5 ≤
                checkedCircuitBudget (.or left right) n := by
            have hraw :
                m0 + m1 + m2 + m3 + m4 + m5 ≤
                  checkedLoopStepEnvelope n +
                    checkedCircuitBudget left n +
                    checkedLoopStepEnvelope n +
                    checkedCircuitBudget right n +
                    checkedLoopStepEnvelope n +
                    checkedLoopStepEnvelope n := by
              omega
            let E := checkedLoopStepEnvelope n
            have hcoef :
                8 * (evalStepCount left + 1) +
                    8 * (evalStepCount right + 1) + 4 ≤
                  8 * (evalStepCount left + evalStepCount right + 4) := by
              omega
            have hmul := Nat.mul_le_mul_right E hcoef
            have hcount :
                evalStepCount (.or left right) + 1 =
                  evalStepCount left + evalStepCount right + 4 := by
              simp [evalStepCount]
              omega
            have hcap :
                checkedLoopStepEnvelope n +
                    checkedCircuitBudget left n +
                    checkedLoopStepEnvelope n +
                    checkedCircuitBudget right n +
                    checkedLoopStepEnvelope n +
                    checkedLoopStepEnvelope n ≤
                  checkedCircuitBudget (.or left right) n := by
              calc
                checkedLoopStepEnvelope n +
                      checkedCircuitBudget left n +
                      checkedLoopStepEnvelope n +
                      checkedCircuitBudget right n +
                      checkedLoopStepEnvelope n +
                      checkedLoopStepEnvelope n
                    =
                  (8 * (evalStepCount left + 1) +
                    8 * (evalStepCount right + 1) + 4) * E := by
                      unfold checkedCircuitBudget
                      dsimp [E]
                      ring
                _ ≤
                  8 * (evalStepCount left + evalStepCount right + 4) * E :=
                    hmul
                _ = checkedCircuitBudget (.or left right) n := by
                      unfold checkedCircuitBudget
                      rw [hcount]
            exact Nat.le_trans hraw hcap
          refine ⟨m0 + m1 + m2 + m3 + m4 + m5,
            hFinalBudget, cfgFinal, ?_, ?_⟩
          · simpa using hAll
          · change ExactCheckedLoopOutcome witness
              (exitMode mode (.or left right))
              (evalCircuit sigma (.or left right)) [] []
              (consumed + (encodeCircuit (.or left right)).length)
              cfgFinal
            simp [ExactCheckedLoopOutcome] at hout5 ⊢
            simpa [exitMode, childMode, circuitTag, finalValue,
              evalCircuit] using hout5


/-- Exact bounded structural producer for every checked circuit. -/
theorem circuit_exact_bounded_certificate
    (sigma : Assignment)
    (witness : BitString) :
    ∀ (phi : CircuitK1.Circuit) (mode : SyntaxMode),
      ExactBoundedCheckedCircuitRunCertificate sigma witness mode phi := by
  intro phi
  induction phi with
  | input i =>
      intro mode
      exact input_exact_bounded_certificate sigma witness mode i
  | const v =>
      intro mode
      exact const_exact_bounded_certificate sigma witness mode v
  | not child ih =>
      intro mode
      exact neg_exact_bounded_certificate
        sigma witness mode child (ih (childMode mode .neg))
  | and left right ihLeft ihRight =>
      intro mode
      exact and_exact_bounded_certificate
        sigma witness mode left right (ihLeft .cnf) (ihRight .cnf)
  | or left right ihLeft ihRight =>
      intro mode
      exact or_exact_bounded_certificate
        sigma witness mode left right (ihLeft .clause) (ihRight .clause)

#print axioms MCore.Real.P01ExactBoundedCircuitProducer.layout_consume_prefix
#print axioms MCore.Real.P01ExactBoundedCircuitProducer.input_exact_bounded_certificate

end P01ExactBoundedCircuitProducer
end Real
end MCore
