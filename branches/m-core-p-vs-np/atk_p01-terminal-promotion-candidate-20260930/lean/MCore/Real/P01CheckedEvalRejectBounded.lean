import MCore.Real.P01CheckedEvalReject
import MCore.Real.P01ExactBoundedAll
import MCore.Real.P01CheckedEvalRunBoundedHelpers
import MCore.Real.P01CheckedVerifierInvariant

namespace MCore
namespace Real
namespace P01CheckedEvalRejectBounded

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
open P01CheckedEvalRunTagPrefix
open P01CheckedEvalRunBoundedHelpers
open P01CheckedEvalRunBoundedCertificate
open P01CheckedEvalReject
open P01CheckedVerifierInvariant
open P01CheckedVerifierBudget
open P01CheckedVerifierGlobalBudget
open P01ExactBoundedCircuitProducer
open P01ExactBoundedAll
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Bounded analogue of the structural rejection certificate. -/
def BoundedCheckedCircuitRejectCertificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (phi : Circuit) : Prop :=
  modeCheck mode phi = false →
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
      cfg.state = .reject


theorem short_tag_reaches_reject_within_envelope
    (n : Nat)
    (mode : SyntaxMode)
    (witness source frameStack : BitString)
    (consumed padding : Nat)
    (hshort : source.length < 3)
    (hsource : source.length ≤ n)
    (hframes : frameStack.length ≤ n) :
    ∃ m ≤ checkedLoopStepEnvelope n,
      ∃ tape : Tape (Option Bool),
        ({ state := .reject, tape := tape } : CheckedConfig) ∈
          checkedEvalRunLoopMachine.runBranches m
            [{ state := .need mode needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed
                   source frameStack padding }] := by
  obtain ⟨m, hm, tape, hrun⟩ :=
    short_tag_source_reaches_reject
      mode witness source frameStack consumed padding hshort
  have hfuel :
      checkedShortTagRejectFuel source frameStack ≤ 8 * (n + 1) := by
    unfold checkedShortTagRejectFuel
    omega
  have hsq : n + 1 ≤ (n + 1)^2 := by
    have hpos : 1 ≤ n + 1 := by omega
    calc
      n + 1 = (n + 1) * 1 := by simp
      _ ≤ (n + 1) * (n + 1) :=
        Nat.mul_le_mul_left (n + 1) hpos
      _ = (n + 1)^2 := by simp [Nat.pow_two]
  have h8 :
      8 * (n + 1) ≤ 8 * (n + 1)^2 :=
    Nat.mul_le_mul_left 8 hsq
  have h256 :
      8 * (n + 1)^2 ≤ 256 * (n + 1)^2 :=
    Nat.mul_le_mul_right ((n + 1)^2) (by omega)
  refine ⟨m, Nat.le_trans hm ?_, tape, hrun⟩
  unfold checkedLoopStepEnvelope
  exact Nat.le_trans hfuel (Nat.le_trans h8 h256)

#print axioms MCore.Real.P01CheckedEvalRejectBounded.short_tag_reaches_reject_within_envelope

/-- A forbidden root tag rejects inside the common checked-loop envelope. -/
theorem disallowed_tag_prefix_reaches_reject_within_envelope
    (n : Nat)
    (mode : SyntaxMode)
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool)
    (hdisallowed :
      tagAllowed mode
        (P01NeedExprTagDecode.decodeTagBits b0 b1 b2) = false)
    (hsource : (b0 :: b1 :: b2 :: rest).length ≤ n)
    (hframes : frameStack.length ≤ n) :
    ∃ m ≤ checkedLoopStepEnvelope n,
      ({ state := .reject,
         tape :=
           evalCursorReadTape witness (consumed + 3)
             rest frameStack padding } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest)
                 frameStack padding }] := by
  obtain ⟨m, hm, hrun⟩ :=
    disallowed_tag_prefix_reaches_reject
      mode witness rest frameStack consumed padding
      b0 b1 b2 hdisallowed
  have hp :=
    checkedTagPrefixFuel_le_envelope n
      (b0 :: b1 :: b2 :: rest) frameStack hsource hframes
  refine ⟨m, Nat.le_trans hm ?_, hrun⟩
  exact Nat.le_trans hp (checkedStepEnvelope_le_loopEnvelope n)

private theorem envelope_plus_unary_budget_le
    (child : Circuit) (n : Nat) :
    checkedLoopStepEnvelope n + checkedCircuitBudget child n ≤
      checkedCircuitBudget (.not child) n := by
  let E := checkedLoopStepEnvelope n
  have hcoef :
      1 + 8 * (evalStepCount child + 1) ≤
        8 * (evalStepCount child + 3) := by omega
  have hmul := Nat.mul_le_mul_right E hcoef
  have hcount :
      evalStepCount (.not child) + 1 =
        evalStepCount child + 3 := by
    simp [evalStepCount]
    omega
  calc
    checkedLoopStepEnvelope n + checkedCircuitBudget child n
        = (1 + 8 * (evalStepCount child + 1)) * E := by
            unfold checkedCircuitBudget
            dsimp [E]
            rw [Nat.add_mul, Nat.one_mul]
    _ ≤ 8 * (evalStepCount child + 3) * E := hmul
    _ = checkedCircuitBudget (.not child) n := by
          unfold checkedCircuitBudget
          rw [hcount]

private theorem binary_left_reject_cap
    (left right : Circuit) (n : Nat) :
    checkedLoopStepEnvelope n + checkedCircuitBudget left n ≤
      8 * (evalStepCount left + evalStepCount right + 4) *
        checkedLoopStepEnvelope n := by
  let E := checkedLoopStepEnvelope n
  have hcoef :
      1 + 8 * (evalStepCount left + 1) ≤
        8 * (evalStepCount left + evalStepCount right + 4) := by omega
  have hmul := Nat.mul_le_mul_right E hcoef
  calc
    checkedLoopStepEnvelope n + checkedCircuitBudget left n
        = (1 + 8 * (evalStepCount left + 1)) * E := by
            unfold checkedCircuitBudget
            dsimp [E]
            rw [Nat.add_mul, Nat.one_mul]
    _ ≤ 8 * (evalStepCount left + evalStepCount right + 4) * E := hmul

private theorem binary_right_reject_cap
    (left right : Circuit) (n : Nat) :
    checkedLoopStepEnvelope n +
        checkedCircuitBudget left n +
        checkedLoopStepEnvelope n +
        checkedCircuitBudget right n ≤
      8 * (evalStepCount left + evalStepCount right + 4) *
        checkedLoopStepEnvelope n := by
  let E := checkedLoopStepEnvelope n
  have hcoef :
      1 + 8 * (evalStepCount left + 1) + 1 +
          8 * (evalStepCount right + 1) ≤
        8 * (evalStepCount left + evalStepCount right + 4) := by omega
  have hmul := Nat.mul_le_mul_right E hcoef
  calc
    checkedLoopStepEnvelope n +
          checkedCircuitBudget left n +
          checkedLoopStepEnvelope n +
          checkedCircuitBudget right n
        =
      (1 + 8 * (evalStepCount left + 1) + 1 +
          8 * (evalStepCount right + 1)) * E := by
            unfold checkedCircuitBudget
            dsimp [E]
            simp only [Nat.add_mul, Nat.one_mul]
            ac_rfl
    _ ≤ 8 * (evalStepCount left + evalStepCount right + 4) * E := hmul

theorem input_bounded_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (i : Nat) :
    BoundedCheckedCircuitRejectCertificate
      sigma witness mode (.input i) := by
  intro hinvalid
  cases mode <;>
    simp [modeCheck, tagAllowed, isCNFBool, isClauseBool] at hinvalid

theorem const_bounded_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (v : Bool) :
    BoundedCheckedCircuitRejectCertificate
      sigma witness mode (.const v) := by
  intro hinvalid tail frames consumed padding n hLayout hlen hread
  have hroot :
      tagAllowed mode (circuitTag (.const v)) = false := by
    cases v <;> cases mode <;>
      simp [modeCheck, tagAllowed, circuitTag,
        isCNFBool, isClauseBool] at hinvalid ⊢
  cases v with
  | false =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject_within_envelope
          n mode witness tail (encodeEvalFrames frames)
          consumed padding false false true
          (by simpa [circuitTag] using hroot)
          (by simpa [encodeCircuit] using hLayout.source_le)
          hLayout.frames_le
      let cfg : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 3)
              tail (encodeEvalFrames frames) padding }
      refine ⟨m, Nat.le_trans hm
        (loopEnvelope_le_checkedCircuitBudget (.const false) n),
        cfg, ?_, rfl⟩
      simpa [cfg, encodeCircuit] using hrun
  | true =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject_within_envelope
          n mode witness tail (encodeEvalFrames frames)
          consumed padding false true false
          (by simpa [circuitTag] using hroot)
          (by simpa [encodeCircuit] using hLayout.source_le)
          hLayout.frames_le
      let cfg : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 3)
              tail (encodeEvalFrames frames) padding }
      refine ⟨m, Nat.le_trans hm
        (loopEnvelope_le_checkedCircuitBudget (.const true) n),
        cfg, ?_, rfl⟩
      simpa [cfg, encodeCircuit] using hrun

theorem not_bounded_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (child : Circuit)
    (hchild :
      BoundedCheckedCircuitRejectCertificate
        sigma witness (childMode mode .neg) child) :
    BoundedCheckedCircuitRejectCertificate
      sigma witness mode (.not child) := by
  intro hinvalid tail frames consumed padding n hLayout hlen hread
  cases hroot : tagAllowed mode .neg with
  | false =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject_within_envelope
          n mode witness (encodeCircuit child ++ tail)
          (encodeEvalFrames frames) consumed padding
          false true true (by simpa using hroot)
          (by simpa [encodeCircuit, List.append_assoc] using hLayout.source_le)
          hLayout.frames_le
      let cfg : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 3)
              (encodeCircuit child ++ tail)
              (encodeEvalFrames frames) padding }
      refine ⟨m, Nat.le_trans hm
        (loopEnvelope_le_checkedCircuitBudget (.not child) n),
        cfg, ?_, rfl⟩
      simpa [cfg, encodeCircuit, List.append_assoc] using hrun
  | true =>
      have hchildInvalid :
          modeCheck (childMode mode .neg) child = false := by
        rw [modeCheck_not] at hinvalid
        simpa [hroot] using hinvalid
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
          false true true .neg .neg rfl hroot rfl
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
      obtain ⟨m1, hm1, cfgReject, h1, hrej⟩ :=
        hchild hchildInvalid tail (.neg :: frames)
          (consumed + 3) padChild n
          (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutChild)
          hlenChild hreadChild
      have h1' :
          cfgReject ∈
            checkedEvalRunLoopMachine.runBranches m1 [cNeed] := by
        simpa [cNeed, encodeEvalFrames, List.append_assoc] using h1
      have hAll :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          m0 m1
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.not child) ++ tail)
                 (encodeEvalFrames frames) padding }]
          cNeed cfgReject h0' h1'
      have hbudget :
          m0 + m1 ≤ checkedCircuitBudget (.not child) n := by
        exact Nat.le_trans (by omega)
          (envelope_plus_unary_budget_le child n)
      exact ⟨m0 + m1, hbudget, cfgReject, hAll, hrej⟩

theorem and_bounded_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (left right : Circuit)
    (hleftReject :
      BoundedCheckedCircuitRejectCertificate sigma witness .cnf left)
    (hrightReject :
      BoundedCheckedCircuitRejectCertificate sigma witness .cnf right) :
    ∀ mode : SyntaxMode,
      BoundedCheckedCircuitRejectCertificate
        sigma witness mode (.and left right) := by
  intro mode hinvalid tail frames consumed padding n hLayout hlen hread
  cases mode with
  | clause =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject_within_envelope
          n .clause witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false false (by rfl)
          (by simpa [encodeCircuit, List.append_assoc] using hLayout.source_le)
          hLayout.frames_le
      let cfg : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 3)
              (encodeCircuit left ++ encodeCircuit right ++ tail)
              (encodeEvalFrames frames) padding }
      refine ⟨m, Nat.le_trans hm
        (loopEnvelope_le_checkedCircuitBudget (.and left right) n),
        cfg, ?_, rfl⟩
      simpa [cfg, encodeCircuit, List.append_assoc] using hrun
  | mustInput =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject_within_envelope
          n .mustInput witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false false (by rfl)
          (by simpa [encodeCircuit, List.append_assoc] using hLayout.source_le)
          hLayout.frames_le
      let cfg : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 3)
              (encodeCircuit left ++ encodeCircuit right ++ tail)
              (encodeEvalFrames frames) padding }
      refine ⟨m, Nat.le_trans hm
        (loopEnvelope_le_checkedCircuitBudget (.and left right) n),
        cfg, ?_, rfl⟩
      simpa [cfg, encodeCircuit, List.append_assoc] using hrun
  | cnf =>
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
          true false false .and .andLeft rfl (by rfl) (by rfl)
          hLayout0.source_le hLayout0.frames_le
      let padLeft := ((padding - 1) - 1) - 1
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
        simpa [cNeedLeft, padLeft, encodeCircuit,
          childMode, List.append_assoc] using h0
      cases hleftMode : modeCheck .cnf left with
      | false =>
          obtain ⟨m1, hm1, cfgReject, h1, hrej⟩ :=
            hleftReject hleftMode
              (encodeCircuit right ++ tail) (.andLeft :: frames)
              (consumed + 3) padLeft n
              (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
              hlenLeft hreadLeft
          have h1' :
              cfgReject ∈
                checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
            simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.and left right) ++ tail)
                     (encodeEvalFrames frames) padding }]
              cNeedLeft cfgReject h0' h1'
          have hcap :
              checkedLoopStepEnvelope n + checkedCircuitBudget left n ≤
                checkedCircuitBudget (.and left right) n := by
            have hb := binary_left_reject_cap left right n
            have hcount :
                evalStepCount (.and left right) + 1 =
                  evalStepCount left + evalStepCount right + 4 := by
              simp [evalStepCount]
              omega
            unfold checkedCircuitBudget
            rw [hcount]
            exact hb
          exact ⟨m0 + m1, Nat.le_trans (by omega) hcap,
            cfgReject, hAll, hrej⟩
      | true =>
          have hrightMode : modeCheck .cnf right = false := by
            rw [modeCheck_and] at hinvalid
            simpa [tagAllowed, hleftMode] using hinvalid
          obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
            exact_bounded_all sigma witness left .cnf hleftMode
              (encodeCircuit right ++ tail) (.andLeft :: frames)
              (consumed + 3) padLeft n
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
          let leftConsumed :=
            (consumed + 3) + (encodeCircuit left).length
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
          obtain ⟨m3, hm3, cfgReject, h3, hrej⟩ :=
            hrightReject hrightMode tail
              (.andRight (evalCircuit sigma left) :: frames)
              leftConsumed padRight n
              (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutRight)
              hlenRight hreadRight
          have h3' :
              cfgReject ∈
                checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
            simpa [cNeedRight, encodeEvalFrames, List.append_assoc] using h3
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1 + m2) m3
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.and left right) ++ tail)
                     (encodeEvalFrames frames) padding }]
              cNeedRight cfgReject h012 h3'
          have hcap :
              checkedLoopStepEnvelope n +
                  checkedCircuitBudget left n +
                  checkedLoopStepEnvelope n +
                  checkedCircuitBudget right n ≤
                checkedCircuitBudget (.and left right) n := by
            have hb := binary_right_reject_cap left right n
            have hcount :
                evalStepCount (.and left right) + 1 =
                  evalStepCount left + evalStepCount right + 4 := by
              simp [evalStepCount]
              omega
            unfold checkedCircuitBudget
            rw [hcount]
            exact hb
          exact ⟨m0 + m1 + m2 + m3,
            Nat.le_trans (by omega) hcap,
            cfgReject, hAll, hrej⟩

theorem or_bounded_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (left right : Circuit)
    (hleftReject :
      BoundedCheckedCircuitRejectCertificate sigma witness .clause left)
    (hrightReject :
      BoundedCheckedCircuitRejectCertificate sigma witness .clause right) :
    ∀ mode : SyntaxMode,
      BoundedCheckedCircuitRejectCertificate
        sigma witness mode (.or left right) := by
  intro mode hinvalid tail frames consumed padding n hLayout hlen hread
  cases hroot : tagAllowed mode .or with
  | false =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject_within_envelope
          n mode witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false true (by simpa using hroot)
          (by simpa [encodeCircuit, List.append_assoc] using hLayout.source_le)
          hLayout.frames_le
      let cfg : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 3)
              (encodeCircuit left ++ encodeCircuit right ++ tail)
              (encodeEvalFrames frames) padding }
      refine ⟨m, Nat.le_trans hm
        (loopEnvelope_le_checkedCircuitBudget (.or left right) n),
        cfg, ?_, rfl⟩
      simpa [cfg, encodeCircuit, List.append_assoc] using hrun
  | true =>
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
          true false true .or .orLeft rfl hroot
          (by simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
          hLayout0.source_le hLayout0.frames_le
      let padLeft := ((padding - 1) - 1) - 1
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
      cases hleftMode : modeCheck .clause left with
      | false =>
          obtain ⟨m1, hm1, cfgReject, h1, hrej⟩ :=
            hleftReject hleftMode
              (encodeCircuit right ++ tail) (.orLeft :: frames)
              (consumed + 3) padLeft n
              (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
              hlenLeft hreadLeft
          have h1' :
              cfgReject ∈
                checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
            simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.or left right) ++ tail)
                     (encodeEvalFrames frames) padding }]
              cNeedLeft cfgReject h0' h1'
          have hcap :
              checkedLoopStepEnvelope n + checkedCircuitBudget left n ≤
                checkedCircuitBudget (.or left right) n := by
            have hb := binary_left_reject_cap left right n
            have hcount :
                evalStepCount (.or left right) + 1 =
                  evalStepCount left + evalStepCount right + 4 := by
              simp [evalStepCount]
              omega
            unfold checkedCircuitBudget
            rw [hcount]
            exact hb
          exact ⟨m0 + m1, Nat.le_trans (by omega) hcap,
            cfgReject, hAll, hrej⟩
      | true =>
          have hrightMode : modeCheck .clause right = false := by
            rw [modeCheck_or] at hinvalid
            simpa [hroot, hleftMode] using hinvalid
          obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
            exact_bounded_all sigma witness left .clause hleftMode
              (encodeCircuit right ++ tail) (.orLeft :: frames)
              (consumed + 3) padLeft n
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
          let leftConsumed :=
            (consumed + 3) + (encodeCircuit left).length
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
          obtain ⟨m3, hm3, cfgReject, h3, hrej⟩ :=
            hrightReject hrightMode tail
              (.orRight (evalCircuit sigma left) :: frames)
              leftConsumed padRight n
              (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutRight)
              hlenRight hreadRight
          have h3' :
              cfgReject ∈
                checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
            simpa [cNeedRight, encodeEvalFrames, List.append_assoc] using h3
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1 + m2) m3
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.or left right) ++ tail)
                     (encodeEvalFrames frames) padding }]
              cNeedRight cfgReject h012 h3'
          have hcap :
              checkedLoopStepEnvelope n +
                  checkedCircuitBudget left n +
                  checkedLoopStepEnvelope n +
                  checkedCircuitBudget right n ≤
                checkedCircuitBudget (.or left right) n := by
            have hb := binary_right_reject_cap left right n
            have hcount :
                evalStepCount (.or left right) + 1 =
                  evalStepCount left + evalStepCount right + 4 := by
              simp [evalStepCount]
              omega
            unfold checkedCircuitBudget
            rw [hcount]
            exact hb
          exact ⟨m0 + m1 + m2 + m3,
            Nat.le_trans (by omega) hcap,
            cfgReject, hAll, hrej⟩

/-- Total bounded rejection induction for every semantic circuit. -/
theorem bounded_circuit_reject_certificate
    (sigma : Assignment)
    (witness : BitString) :
    ∀ (phi : Circuit) (mode : SyntaxMode),
      BoundedCheckedCircuitRejectCertificate sigma witness mode phi := by
  intro phi
  induction phi with
  | input i =>
      intro mode
      exact input_bounded_reject_certificate sigma witness mode i
  | const v =>
      intro mode
      exact const_bounded_reject_certificate sigma witness mode v
  | not child ih =>
      intro mode
      exact not_bounded_reject_certificate sigma witness mode child
        (ih (childMode mode .neg))
  | and left right ihLeft ihRight =>
      intro mode
      exact and_bounded_reject_certificate sigma witness left right
        (ihLeft .cnf) (ihRight .cnf) mode
  | or left right ihLeft ihRight =>
      intro mode
      exact or_bounded_reject_certificate sigma witness left right
        (ihLeft .clause) (ihRight .clause) mode

#print axioms MCore.Real.P01CheckedEvalRejectBounded.disallowed_tag_prefix_reaches_reject_within_envelope
#print axioms MCore.Real.P01CheckedEvalRejectBounded.bounded_circuit_reject_certificate

end P01CheckedEvalRejectBounded
end Real
end MCore
