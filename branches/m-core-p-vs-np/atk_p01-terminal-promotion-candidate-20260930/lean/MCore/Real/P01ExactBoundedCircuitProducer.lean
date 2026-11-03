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
    (pref rest frameStack : BitString)
    (h :
      CheckedLayoutBound n consumed
        (pref ++ rest) frameStack) :
    CheckedLayoutBound n (consumed + pref.length)
      rest frameStack := by
  constructor
  · have hs := h.source_budget
    simp [List.length_append] at hs ⊢
    omega
  · have hf := h.frames_paid
    omega

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
          inputCheckedEmbed,
          P01InputNodeCompositeRun.inputNodeFinalMode,
          inputAfterReadTarget]
    | nil =>
        cases frames with
        | nil =>
            refine ⟨(inputAfterReadTarget witness finalConsumed
              [] [] padding).tape, ?_⟩
            simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
              cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
              inputCheckedEmbed,
              P01InputNodeCompositeRun.inputNodeFinalMode,
              inputAfterReadTarget]
        | cons f fs =>
            refine ⟨padding, ?_⟩
            cases f with
            | neg =>
                simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
                  inputCheckedEmbed,
                  P01InputNodeCompositeRun.inputNodeFinalMode,
                  inputAfterReadTarget, encodeEvalFrames, encodeEvalFrame]
            | andLeft =>
                simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
                  inputCheckedEmbed,
                  P01InputNodeCompositeRun.inputNodeFinalMode,
                  inputAfterReadTarget, encodeEvalFrames, encodeEvalFrame]
            | andRight a =>
                cases a <;>
                  simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
                    cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
                    inputCheckedEmbed,
                    P01InputNodeCompositeRun.inputNodeFinalMode,
                    inputAfterReadTarget, encodeEvalFrames, encodeEvalFrame]
            | orLeft =>
                simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
                  cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
                  inputCheckedEmbed,
                  P01InputNodeCompositeRun.inputNodeFinalMode,
                  inputAfterReadTarget, encodeEvalFrames, encodeEvalFrame]
            | orRight a =>
                cases a <;>
                  simp [ExactCheckedLoopOutcome, exitMode, circuitTag, childMode,
                    cfg, P01CheckedEvalRunInputTag.inputCheckedConfig,
                    inputCheckedEmbed,
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
            simpa [ExactCheckedLoopOutcome, CheckedLoopOutcome, evalCircuit] using hout3

#print axioms MCore.Real.P01ExactBoundedCircuitProducer.layout_consume_prefix
#print axioms MCore.Real.P01ExactBoundedCircuitProducer.input_exact_bounded_certificate

end P01ExactBoundedCircuitProducer
end Real
end MCore
