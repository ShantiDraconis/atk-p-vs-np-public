import MCore.Real.P01ExactBoundedCircuitProducer

namespace MCore
namespace Real
namespace P01ExactBoundedBinary

open CanonicalFinalProof
open CircuitK1
open CanonicalSATWitness
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBoundedHelpers
open P01CheckedEvalRunBoundedCertificate
open P01CheckedEvalRunBaseCases
open P01CheckedVerifierInvariant
open P01CheckedVerifierGlobalBudget
open P01ExactBoundedCircuitProducer
open P01CNFMode
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

private theorem binary_budget_cap
    (left right : Circuit) (n : Nat) :
    checkedCircuitBudget left n +
        checkedCircuitBudget right n +
        4 * checkedLoopStepEnvelope n ≤
      8 * (evalStepCount left + evalStepCount right + 4) *
        checkedLoopStepEnvelope n := by
  let E := checkedLoopStepEnvelope n
  have hcoef :
      8 * (evalStepCount left + 1) +
          8 * (evalStepCount right + 1) + 4 ≤
        8 * (evalStepCount left + evalStepCount right + 4) := by
    omega
  have heq :
      checkedCircuitBudget left n +
          checkedCircuitBudget right n +
          4 * checkedLoopStepEnvelope n =
        (8 * (evalStepCount left + 1) +
          8 * (evalStepCount right + 1) + 4) * E := by
    unfold checkedCircuitBudget
    dsimp [E]
    rw [Nat.add_mul, Nat.add_mul]
  rw [heq]
  exact Nat.mul_le_mul_right E hcoef

private theorem binary_prefix_budget_cap
    (left right : Circuit) (n : Nat) :
    checkedCircuitBudget left n +
        checkedCircuitBudget right n +
        3 * checkedLoopStepEnvelope n ≤
      8 * (evalStepCount left + evalStepCount right + 4) *
        checkedLoopStepEnvelope n := by
  have h34 :
      3 * checkedLoopStepEnvelope n ≤
        4 * checkedLoopStepEnvelope n :=
    Nat.mul_le_mul_right (checkedLoopStepEnvelope n) (by omega)
  have hadd :
      checkedCircuitBudget left n +
          checkedCircuitBudget right n +
          3 * checkedLoopStepEnvelope n ≤
        checkedCircuitBudget left n +
          checkedCircuitBudget right n +
          4 * checkedLoopStepEnvelope n := by
    exact Nat.add_le_add_left h34
      (checkedCircuitBudget left n + checkedCircuitBudget right n)
  exact Nat.le_trans hadd (binary_budget_cap left right n)

/-- Exact bounded binary producer for conjunction.

The proof maintains the exact consumed source cursor across both recursive
children.  The static CheckedLayoutBound is advanced by the exact encoded
prefix length after the left child and its top frame is replaced from
andLeft to andRight before invoking the right child.
-/
theorem and_exact_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (left right : CircuitK1.Circuit)
    (hleft :
      ExactBoundedCheckedCircuitRunCertificate sigma witness .cnf left)
    (hright :
      ExactBoundedCheckedCircuitRunCertificate sigma witness .cnf right) :
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
        intro i hi
        exact hread i (by
          simpa [varBound] using
            Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
      have hreadRight :
          ∀ i, i < varBound right →
            witness.getD i false = sigma i := by
        intro i hi
        exact hread i (by
          simpa [varBound] using
            Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))

      have hLayout0 :
          CheckedLayoutBound n consumed
            (true :: false :: false ::
              (encodeCircuit left ++ encodeCircuit right ++ tail))
            (encodeEvalFrames frames) := by
        simpa [encodeCircuit, List.append_assoc] using hLayout

      have hLayoutLeft :
          CheckedLayoutBound n (consumed + 3)
            (encodeCircuit left ++ encodeCircuit right ++ tail)
            (encodeEvalFrame .andLeft ++ encodeEvalFrames frames) :=
        after_push_tag n consumed true false false
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) .andLeft hLayout0

      obtain ⟨m0, hm0, h0⟩ :=
        pushTag_checked_reaches_need_within_envelope
          n .cnf witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false false .and .andLeft rfl (by rfl) (by
            simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
          hLayout0.source_le hLayout0.frames_le

      let padLeft := ((padding - 1) - 1) - 1
      let leftConsumed := (consumed + 3) + (encodeCircuit left).length
      let cNeedLeft : CheckedConfig :=
        { state := .need .cnf needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness (consumed + 3)
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
        simpa [cNeedLeft, padLeft, encodeCircuit, List.append_assoc] using h0

      obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
        hleft hleftMode (encodeCircuit right ++ tail)
          (.andLeft :: frames) (consumed + 3) padLeft n
          (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
          hlenLeft hreadLeft

      have h1' :
          cfgLeft ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
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

      have hout1' :
          ∃ padding1,
            cfgLeft =
              { state := .have (exitMode .cnf left)
                  (.start (evalCircuit sigma left)),
                tape :=
                  evalCursorStackEndTape witness leftConsumed
                    (encodeCircuit right ++ tail)
                    (encodeEvalFrames (.andLeft :: frames)) padding1 } := by
        simpa [ExactCheckedLoopOutcome, leftConsumed] using hout1
      rcases hout1' with ⟨padding1, hcfgLeft⟩
      subst cfgLeft

      have hLayoutAfterLeft :
          CheckedLayoutBound n leftConsumed
            (encodeCircuit right ++ tail)
            (encodeEvalFrame .andLeft ++ encodeEvalFrames frames) := by
        simpa [leftConsumed, List.append_assoc] using
          layout_consume_prefix n (consumed + 3)
            (encodeCircuit left) (encodeCircuit right ++ tail)
            (encodeEvalFrame .andLeft ++ encodeEvalFrames frames)
            (by simpa [List.append_assoc] using hLayoutLeft)

      have hLayoutRight :
          CheckedLayoutBound n leftConsumed
            (encodeCircuit right ++ tail)
            (encodeEvalFrame (.andRight (evalCircuit sigma left)) ++
              encodeEvalFrames frames) :=
        replace_top_frame n leftConsumed
          (encodeCircuit right ++ tail) (encodeEvalFrames frames)
          .andLeft (.andRight (evalCircuit sigma left)) hLayoutAfterLeft

      obtain ⟨m2, hm2, h2⟩ :=
        andLeftReturn_checked_reaches_need_within_envelope
          n (exitMode .cnf left) witness
          (encodeCircuit right ++ tail) (encodeEvalFrames frames)
          leftConsumed padding1 (evalCircuit sigma left)

      let padRight := (((padding1 + 3) - 1) - 1) - 1
      let cNeedRight : CheckedConfig :=
        { state := .need .cnf needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness leftConsumed
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
                   evalCursorStackEndTape witness leftConsumed
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
               evalCursorStackEndTape witness leftConsumed
                 (encodeCircuit right ++ tail)
                 (encodeEvalFrames (.andLeft :: frames))
                 padding1 } : CheckedConfig)
          cNeedRight h01 h2'

      obtain ⟨m3, hm3, cfgRight, h3, hout3⟩ :=
        hright hrightMode tail
          (.andRight (evalCircuit sigma left) :: frames)
          leftConsumed padRight n
          (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutRight)
          hlenRight hreadRight

      have h3' :
          cfgRight ∈ checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
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

      let rightConsumed := leftConsumed + (encodeCircuit right).length
      have hout3' :
          ∃ padding2,
            cfgRight =
              { state := .have (exitMode .cnf right)
                  (.start (evalCircuit sigma right)),
                tape :=
                  evalCursorStackEndTape witness rightConsumed tail
                    (encodeEvalFrames
                      (.andRight (evalCircuit sigma left) :: frames))
                    padding2 } := by
        simpa [ExactCheckedLoopOutcome, rightConsumed] using hout3
      rcases hout3' with ⟨padding2, hcfgRight⟩
      subst cfgRight

      obtain ⟨m4, hm4, h4⟩ :=
        andRightReturn_checked_reaches_have_within_envelope
          n (exitMode .cnf right) witness tail
          (encodeEvalFrames frames) rightConsumed padding2
          (evalCircuit sigma left) (evalCircuit sigma right)

      let finalValue :=
        Bool.and (evalCircuit sigma left) (evalCircuit sigma right)
      let cHave : CheckedConfig :=
        { state := .have .cnf (.start finalValue),
          tape :=
            evalCursorStackEndTape witness rightConsumed tail
              (encodeEvalFrames frames) (padding2 + 3) }

      have h4' :
          cHave ∈
            checkedEvalRunLoopMachine.runBranches m4
              [{ state := .have (exitMode .cnf right)
                   (.start (evalCircuit sigma right)),
                 tape :=
                   evalCursorStackEndTape witness rightConsumed tail
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
               evalCursorStackEndTape witness rightConsumed tail
                 (encodeEvalFrames
                   (.andRight (evalCircuit sigma left) :: frames))
                 padding2 } : CheckedConfig)
          cHave h0123 h4'

      have hConsumed :
          rightConsumed =
            consumed + (encodeCircuit (.and left right)).length := by
        unfold rightConsumed leftConsumed
        simp [encodeCircuit, List.length_append]
        omega

      have hExitAnd :
          exitMode .cnf (.and left right) = .cnf := rfl

      have hprefixBudget :
          m0 + m1 + m2 + m3 + m4 ≤
            checkedCircuitBudget (.and left right) n := by
        have hraw :
            m0 + m1 + m2 + m3 + m4 ≤
              checkedCircuitBudget left n +
                checkedCircuitBudget right n +
                3 * checkedLoopStepEnvelope n := by
          omega
        have hcap0 :=
          binary_prefix_budget_cap left right n
        have hcount :
            evalStepCount (.and left right) + 1 =
              evalStepCount left + evalStepCount right + 4 := by
          simp [evalStepCount]
          omega
        have hcap :
            checkedCircuitBudget left n +
                checkedCircuitBudget right n +
                3 * checkedLoopStepEnvelope n ≤
              checkedCircuitBudget (.and left right) n := by
          unfold checkedCircuitBudget
          rw [hcount]
          exact hcap0
        exact Nat.le_trans hraw hcap

      cases tail with
      | cons b bs =>
          refine ⟨m0 + m1 + m2 + m3 + m4,
            hprefixBudget, cHave, h01234, ?_⟩
          change ExactCheckedLoopOutcome witness
            (exitMode .cnf (.and left right))
            (evalCircuit sigma (.and left right))
            (b :: bs) frames
            (consumed + (encodeCircuit (.and left right)).length) cHave
          rw [hExitAnd, ← hConsumed]
          refine ⟨padding2 + 3, ?_⟩
          simp [ExactCheckedLoopOutcome, cHave, finalValue, evalCircuit]
      | nil =>
          cases frames with
          | cons f fs =>
              refine ⟨m0 + m1 + m2 + m3 + m4,
                hprefixBudget, cHave, h01234, ?_⟩
              change ExactCheckedLoopOutcome witness
                (exitMode .cnf (.and left right))
                (evalCircuit sigma (.and left right))
                [] (f :: fs)
                (consumed + (encodeCircuit (.and left right)).length) cHave
              rw [hExitAnd, ← hConsumed]
              refine ⟨padding2 + 3, ?_⟩
              simp [ExactCheckedLoopOutcome, cHave, finalValue, evalCircuit]
          | nil =>
              obtain ⟨m5, hm5, cfgFinal, h5, hout5⟩ :=
                have_reaches_outcome_within_envelope
                  n .cnf witness finalValue [] []
                  rightConsumed (padding2 + 3)
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
              have hfinalBudget :
                  m0 + m1 + m2 + m3 + m4 + m5 ≤
                    checkedCircuitBudget (.and left right) n := by
                have hraw :
                    m0 + m1 + m2 + m3 + m4 + m5 ≤
                      checkedCircuitBudget left n +
                        checkedCircuitBudget right n +
                        4 * checkedLoopStepEnvelope n := by
                  omega
                have hcap0 := binary_budget_cap left right n
                have hcount :
                    evalStepCount (.and left right) + 1 =
                      evalStepCount left + evalStepCount right + 4 := by
                  simp [evalStepCount]
                  omega
                have hcap :
                    checkedCircuitBudget left n +
                        checkedCircuitBudget right n +
                        4 * checkedLoopStepEnvelope n ≤
                      checkedCircuitBudget (.and left right) n := by
                  unfold checkedCircuitBudget
                  rw [hcount]
                  exact hcap0
                exact Nat.le_trans hraw hcap
              refine ⟨m0 + m1 + m2 + m3 + m4 + m5,
                hfinalBudget, cfgFinal, ?_, ?_⟩
              · simpa using hAll
              · change ExactCheckedLoopOutcome witness
                  (exitMode .cnf (.and left right))
                  (evalCircuit sigma (.and left right)) [] []
                  (consumed + (encodeCircuit (.and left right)).length) cfgFinal
                simpa [ExactCheckedLoopOutcome, CheckedLoopOutcome,
                  finalValue, evalCircuit, exitMode, circuitTag, childMode] using hout5

/-- Exact bounded binary producer for disjunction.  The argument mirrors the
AND producer, but the recursive children and continuation mode are clause.
-/
theorem or_exact_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (left right : CircuitK1.Circuit)
    (hleft :
      ExactBoundedCheckedCircuitRunCertificate sigma witness .clause left)
    (hright :
      ExactBoundedCheckedCircuitRunCertificate sigma witness .clause right) :
    ExactBoundedCheckedCircuitRunCertificate
      sigma witness mode (.or left right) := by
  intro hmode tail frames consumed padding n hLayout hlen hread

  have hparts :
      (tagAllowed mode .or = true ∧ modeCheck .clause left = true) ∧
        modeCheck .clause right = true := by
    have h := hmode
    rw [modeCheck_or] at h
    simpa using h
  have hAllowed := hparts.1.1
  have hleftMode := hparts.1.2
  have hrightMode := hparts.2

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
    intro i hi
    exact hread i (by
      simpa [varBound] using
        Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
  have hreadRight :
      ∀ i, i < varBound right →
        witness.getD i false = sigma i := by
    intro i hi
    exact hread i (by
      simpa [varBound] using
        Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))

  have hLayout0 :
      CheckedLayoutBound n consumed
        (true :: false :: true ::
          (encodeCircuit left ++ encodeCircuit right ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using hLayout

  have hLayoutLeft :
      CheckedLayoutBound n (consumed + 3)
        (encodeCircuit left ++ encodeCircuit right ++ tail)
        (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) :=
    after_push_tag n consumed true false true
      (encodeCircuit left ++ encodeCircuit right ++ tail)
      (encodeEvalFrames frames) .orLeft hLayout0

  obtain ⟨m0, hm0, h0⟩ :=
    pushTag_checked_reaches_need_within_envelope
      n mode witness
      (encodeCircuit left ++ encodeCircuit right ++ tail)
      (encodeEvalFrames frames) consumed padding
      true false true .or .orLeft rfl hAllowed (by
        simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
      hLayout0.source_le hLayout0.frames_le

  let padLeft := ((padding - 1) - 1) - 1
  let leftConsumed := (consumed + 3) + (encodeCircuit left).length
  let cNeedLeft : CheckedConfig :=
    { state := .need .clause needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
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
    simpa [cNeedLeft, padLeft, encodeCircuit, childMode,
      List.append_assoc] using h0

  obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
    hleft hleftMode (encodeCircuit right ++ tail)
      (.orLeft :: frames) (consumed + 3) padLeft n
      (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
      hlenLeft hreadLeft

  have h1' :
      cfgLeft ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
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

  have hout1' :
      ∃ padding1,
        cfgLeft =
          { state := .have (exitMode .clause left)
              (.start (evalCircuit sigma left)),
            tape :=
              evalCursorStackEndTape witness leftConsumed
                (encodeCircuit right ++ tail)
                (encodeEvalFrames (.orLeft :: frames)) padding1 } := by
    simpa [ExactCheckedLoopOutcome, leftConsumed] using hout1
  rcases hout1' with ⟨padding1, hcfgLeft⟩
  subst cfgLeft

  have hLayoutAfterLeft :
      CheckedLayoutBound n leftConsumed
        (encodeCircuit right ++ tail)
        (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) := by
    simpa [leftConsumed, List.append_assoc] using
      layout_consume_prefix n (consumed + 3)
        (encodeCircuit left) (encodeCircuit right ++ tail)
        (encodeEvalFrame .orLeft ++ encodeEvalFrames frames)
        (by simpa [List.append_assoc] using hLayoutLeft)

  have hLayoutRight :
      CheckedLayoutBound n leftConsumed
        (encodeCircuit right ++ tail)
        (encodeEvalFrame (.orRight (evalCircuit sigma left)) ++
          encodeEvalFrames frames) :=
    replace_top_frame n leftConsumed
      (encodeCircuit right ++ tail) (encodeEvalFrames frames)
      .orLeft (.orRight (evalCircuit sigma left)) hLayoutAfterLeft

  obtain ⟨m2, hm2, h2⟩ :=
    orLeftReturn_checked_reaches_need_within_envelope
      n (exitMode .clause left) witness
      (encodeCircuit right ++ tail) (encodeEvalFrames frames)
      leftConsumed padding1 (evalCircuit sigma left)

  let padRight := (((padding1 + 3) - 1) - 1) - 1
  let cNeedRight : CheckedConfig :=
    { state := .need .clause needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness leftConsumed
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
               evalCursorStackEndTape witness leftConsumed
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
           evalCursorStackEndTape witness leftConsumed
             (encodeCircuit right ++ tail)
             (encodeEvalFrames (.orLeft :: frames))
             padding1 } : CheckedConfig)
      cNeedRight h01 h2'

  obtain ⟨m3, hm3, cfgRight, h3, hout3⟩ :=
    hright hrightMode tail
      (.orRight (evalCircuit sigma left) :: frames)
      leftConsumed padRight n
      (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutRight)
      hlenRight hreadRight

  have h3' :
      cfgRight ∈ checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
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

  let rightConsumed := leftConsumed + (encodeCircuit right).length
  have hout3' :
      ∃ padding2,
        cfgRight =
          { state := .have (exitMode .clause right)
              (.start (evalCircuit sigma right)),
            tape :=
              evalCursorStackEndTape witness rightConsumed tail
                (encodeEvalFrames
                  (.orRight (evalCircuit sigma left) :: frames))
                padding2 } := by
    simpa [ExactCheckedLoopOutcome, rightConsumed] using hout3
  rcases hout3' with ⟨padding2, hcfgRight⟩
  subst cfgRight

  obtain ⟨m4, hm4, h4⟩ :=
    orRightReturn_checked_reaches_have_within_envelope
      n (exitMode .clause right) witness tail
      (encodeEvalFrames frames) rightConsumed padding2
      (evalCircuit sigma left) (evalCircuit sigma right)

  let finalValue :=
    Bool.or (evalCircuit sigma left) (evalCircuit sigma right)
  let cHave : CheckedConfig :=
    { state := .have .clause (.start finalValue),
      tape :=
        evalCursorStackEndTape witness rightConsumed tail
          (encodeEvalFrames frames) (padding2 + 3) }

  have h4' :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches m4
          [{ state := .have (exitMode .clause right)
               (.start (evalCircuit sigma right)),
             tape :=
               evalCursorStackEndTape witness rightConsumed tail
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
           evalCursorStackEndTape witness rightConsumed tail
             (encodeEvalFrames
               (.orRight (evalCircuit sigma left) :: frames))
             padding2 } : CheckedConfig)
      cHave h0123 h4'

  have hConsumed :
      rightConsumed =
        consumed + (encodeCircuit (.or left right)).length := by
    unfold rightConsumed leftConsumed
    simp [encodeCircuit, List.length_append]
    omega

  have hExit :
      exitMode mode (.or left right) = .clause := by
    simp [exitMode, circuitTag, childMode]

  have hprefixBudget :
      m0 + m1 + m2 + m3 + m4 ≤
        checkedCircuitBudget (.or left right) n := by
    have hraw :
        m0 + m1 + m2 + m3 + m4 ≤
          checkedCircuitBudget left n +
            checkedCircuitBudget right n +
            3 * checkedLoopStepEnvelope n := by
      omega
    have hcap0 := binary_prefix_budget_cap left right n
    have hcount :
        evalStepCount (.or left right) + 1 =
          evalStepCount left + evalStepCount right + 4 := by
      simp [evalStepCount]
      omega
    have hcap :
        checkedCircuitBudget left n +
            checkedCircuitBudget right n +
            3 * checkedLoopStepEnvelope n ≤
          checkedCircuitBudget (.or left right) n := by
      unfold checkedCircuitBudget
      rw [hcount]
      exact hcap0
    exact Nat.le_trans hraw hcap

  cases tail with
  | cons b bs =>
      refine ⟨m0 + m1 + m2 + m3 + m4,
        hprefixBudget, cHave, h01234, ?_⟩
      change ExactCheckedLoopOutcome witness
        (exitMode mode (.or left right))
        (evalCircuit sigma (.or left right))
        (b :: bs) frames
        (consumed + (encodeCircuit (.or left right)).length) cHave
      rw [hExit, ← hConsumed]
      refine ⟨padding2 + 3, ?_⟩
      simp [ExactCheckedLoopOutcome, cHave, finalValue, evalCircuit]
  | nil =>
      cases frames with
      | cons f fs =>
          refine ⟨m0 + m1 + m2 + m3 + m4,
            hprefixBudget, cHave, h01234, ?_⟩
          change ExactCheckedLoopOutcome witness
            (exitMode mode (.or left right))
            (evalCircuit sigma (.or left right))
            [] (f :: fs)
            (consumed + (encodeCircuit (.or left right)).length) cHave
          rw [hExit, ← hConsumed]
          refine ⟨padding2 + 3, ?_⟩
          simp [ExactCheckedLoopOutcome, cHave, finalValue, evalCircuit]
      | nil =>
          obtain ⟨m5, hm5, cfgFinal, h5, hout5⟩ :=
            have_reaches_outcome_within_envelope
              n .clause witness finalValue [] []
              rightConsumed (padding2 + 3)
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
          have hfinalBudget :
              m0 + m1 + m2 + m3 + m4 + m5 ≤
                checkedCircuitBudget (.or left right) n := by
            have hraw :
                m0 + m1 + m2 + m3 + m4 + m5 ≤
                  checkedCircuitBudget left n +
                    checkedCircuitBudget right n +
                    4 * checkedLoopStepEnvelope n := by
              omega
            have hcap0 := binary_budget_cap left right n
            have hcount :
                evalStepCount (.or left right) + 1 =
                  evalStepCount left + evalStepCount right + 4 := by
              simp [evalStepCount]
              omega
            have hcap :
                checkedCircuitBudget left n +
                    checkedCircuitBudget right n +
                    4 * checkedLoopStepEnvelope n ≤
                  checkedCircuitBudget (.or left right) n := by
              unfold checkedCircuitBudget
              rw [hcount]
              exact hcap0
            exact Nat.le_trans hraw hcap
          refine ⟨m0 + m1 + m2 + m3 + m4 + m5,
            hfinalBudget, cfgFinal, ?_, ?_⟩
          · simpa using hAll
          · change ExactCheckedLoopOutcome witness
              (exitMode mode (.or left right))
              (evalCircuit sigma (.or left right)) [] []
              (consumed + (encodeCircuit (.or left right)).length) cfgFinal
            simpa [ExactCheckedLoopOutcome, CheckedLoopOutcome,
              finalValue, evalCircuit, exitMode, circuitTag, childMode] using hout5

#print axioms MCore.Real.P01ExactBoundedBinary.and_exact_bounded_certificate
#print axioms MCore.Real.P01ExactBoundedBinary.or_exact_bounded_certificate

end P01ExactBoundedBinary
end Real
end MCore
