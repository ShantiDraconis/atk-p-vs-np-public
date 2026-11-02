import MCore.Real.P01CheckedEvalRunTagPrefix
import MCore.Real.CanonicalCircuitBits
import MCore.Real.P01EncodedFrameTape
import MCore.Real.P01CheckedEvalRunNeedTags
import MCore.Real.P01CheckedEvalRunCircuitCertificate

namespace MCore
namespace Real
namespace P01CheckedEvalReject

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix
open P01CheckedEvalRunNeedTags
open P01NTMRunLaws
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunHaveValue
open P01CheckedEvalRunCircuitCertificate

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- If the canonical root tag of a circuit is forbidden by the current syntax
mode, the checked evaluator physically rejects after the common
seek/decode/check prefix.

This is the root-rejection producer.  It contains no recursive semantic
assumption about children. -/
theorem root_disallowed_reaches_reject
    (mode : SyntaxMode)
    (witness : BitString)
    (phi : Circuit)
    (tail : BitString)
    (frames : List P01EncodedStackEvaluator.EvalFrame)
    (consumed padding : Nat)
    (hroot :
      tagAllowed mode (circuitTag phi) = false) :
    ∃ m,
      ({ state := .reject,
         tape :=
           evalCursorReadTape witness (consumed + 3)
             ((encodeCircuit phi).drop 3 ++ tail)
             (encodeEvalFrames frames) padding } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit phi ++ tail)
                 (encodeEvalFrames frames) padding }] := by
  cases phi with
  | input i =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject
          mode witness (encodeNat i ++ tail)
          (encodeEvalFrames frames) consumed padding
          false false false hroot
      refine ⟨m, ?_⟩
      simpa [encodeCircuit, circuitTag, List.append_assoc] using hrun
  | const v =>
      cases v with
      | false =>
          obtain ⟨m, hm, hrun⟩ :=
            disallowed_tag_prefix_reaches_reject
              mode witness tail (encodeEvalFrames frames)
              consumed padding false false true hroot
          refine ⟨m, ?_⟩
          simpa [encodeCircuit, circuitTag] using hrun
      | true =>
          obtain ⟨m, hm, hrun⟩ :=
            disallowed_tag_prefix_reaches_reject
              mode witness tail (encodeEvalFrames frames)
              consumed padding false true false hroot
          refine ⟨m, ?_⟩
          simpa [encodeCircuit, circuitTag] using hrun
  | not child =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject
          mode witness (encodeCircuit child ++ tail)
          (encodeEvalFrames frames) consumed padding
          false true true hroot
      refine ⟨m, ?_⟩
      simpa [encodeCircuit, circuitTag, List.append_assoc] using hrun
  | and left right =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject
          mode witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false false hroot
      refine ⟨m, ?_⟩
      simpa [encodeCircuit, circuitTag, List.append_assoc] using hrun
  | or left right =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject
          mode witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false true hroot
      refine ⟨m, ?_⟩
      simpa [encodeCircuit, circuitTag, List.append_assoc] using hrun

/-- In must-input mode, every failing semantic check is already visible
at the root tag: the only admitted circuit form is an input node. -/
theorem mustInput_root_disallowed_of_check_false
    (phi : Circuit)
    (h : modeCheck .mustInput phi = false) :
    tagAllowed .mustInput (circuitTag phi) = false := by
  cases phi with
  | input i =>
      simp [modeCheck] at h
  | const v =>
      cases v <;> rfl
  | not c =>
      rfl
  | and a b =>
      rfl
  | or a b =>
      rfl

/-- A syntactically invalid negation is physically rejected.

If the current mode forbids the negation tag, rejection happens at the root.
Otherwise negation switches to must-input mode; any invalid child then has a
root-disallowed tag, so the already-certified root rejection producer applies
after the physical neg-frame push. -/
theorem invalid_not_reaches_reject
    (mode : SyntaxMode)
    (witness : BitString)
    (child : Circuit)
    (tail : BitString)
    (frames : List P01EncodedStackEvaluator.EvalFrame)
    (consumed padding : Nat)
    (hinvalid : modeCheck mode (.not child) = false) :
    ∃ m cfg,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (encodeCircuit (.not child) ++ tail)
               (encodeEvalFrames frames) padding }] ∧
      cfg.state = .reject := by
  cases hroot : tagAllowed mode .neg with
  | false =>
      have hroot' :
          tagAllowed mode (circuitTag (.not child)) = false := by
        simpa [circuitTag] using hroot
      obtain ⟨m, hrun⟩ :=
        root_disallowed_reaches_reject
          mode witness (.not child) tail frames consumed padding hroot'
      let cfg : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 3)
              ((encodeCircuit (.not child)).drop 3 ++ tail)
              (encodeEvalFrames frames) padding }
      exact ⟨m, cfg, by simpa [cfg] using hrun, rfl⟩
  | true =>
      have hchild :
          modeCheck .mustInput child = false := by
        rw [modeCheck_not] at hinvalid
        simpa [hroot, childMode] using hinvalid
      have hchildRoot :
          tagAllowed .mustInput (circuitTag child) = false :=
        mustInput_root_disallowed_of_check_false child hchild

      obtain ⟨m0, h0⟩ :=
        neg_checked_reaches_need
          mode witness (encodeCircuit child ++ tail)
          (encodeEvalFrames frames) consumed padding hroot

      let padChild := ((padding - 1) - 1) - 1
      let cChild : CheckedConfig :=
        { state := .need .mustInput needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness (consumed + 3)
              (encodeCircuit child ++ tail)
              (encodeEvalFrames (.neg :: frames)) padChild }

      have h0' :
          cChild ∈ checkedEvalRunLoopMachine.runBranches m0
            [{ state := .need mode needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed
                   (encodeCircuit (.not child) ++ tail)
                   (encodeEvalFrames frames) padding }] := by
        simpa [cChild, padChild, encodeCircuit,
          encodeEvalFrames, List.append_assoc] using h0

      obtain ⟨m1, h1⟩ :=
        root_disallowed_reaches_reject
          .mustInput witness child tail (.neg :: frames)
          (consumed + 3) padChild hchildRoot

      let cReject : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 6)
              ((encodeCircuit child).drop 3 ++ tail)
              (encodeEvalFrames (.neg :: frames)) padChild }

      have h1' :
          cReject ∈ checkedEvalRunLoopMachine.runBranches m1 [cChild] := by
        simpa [cReject, cChild] using h1

      have hAll :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          m0 m1
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.not child) ++ tail)
                 (encodeEvalFrames frames) padding }]
          cChild cReject h0' h1'

      exact ⟨m0 + m1, cReject, hAll, rfl⟩

/-- Producer-first rejection certificate for one circuit under one syntax
mode.  It is dual to `CheckedCircuitRunCertificate`: a failing mode check must
lead the physical checked loop to its reject state, while preserving arbitrary
external source tail and continuation stack. -/
def CheckedCircuitRejectCertificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (phi : Circuit) : Prop :=
  modeCheck mode phi = false →
  ∀ (tail : BitString)
      (frames : List P01EncodedStackEvaluator.EvalFrame)
      (consumed padding : Nat),
    varBound phi ≤ witness.length →
    (∀ i, i < varBound phi →
      witness.getD i false = sigma i) →
    ∃ m cfg,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (encodeCircuit phi ++ tail)
               (encodeEvalFrames frames) padding }] ∧
      cfg.state = .reject

/-- Input nodes are admitted by every syntax mode, so an invalid-input
certificate is vacuous. -/
theorem input_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (i : Nat) :
    CheckedCircuitRejectCertificate sigma witness mode (.input i) := by
  intro hinvalid
  cases mode <;>
    simp [modeCheck, tagAllowed, isCNFBool, isClauseBool] at hinvalid

/-- Constants rejected by a syntax mode are rejected immediately at their root
tag. -/
theorem const_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (v : Bool) :
    CheckedCircuitRejectCertificate sigma witness mode (.const v) := by
  intro hinvalid tail frames consumed padding hlen hread
  have hroot :
      tagAllowed mode (circuitTag (.const v)) = false := by
    cases v <;> cases mode <;>
      simp [modeCheck, tagAllowed, circuitTag,
        isCNFBool, isClauseBool] at hinvalid ⊢
  obtain ⟨m, hrun⟩ :=
    root_disallowed_reaches_reject
      mode witness (.const v) tail frames consumed padding hroot
  let cfg : CheckedConfig :=
    { state := .reject,
      tape :=
        evalCursorReadTape witness (consumed + 3)
          ((encodeCircuit (.const v)).drop 3 ++ tail)
          (encodeEvalFrames frames) padding }
  exact ⟨m, cfg, by simpa [cfg] using hrun, rfl⟩

/-- Negation rejection certificate: invalid negation is already completely
handled by the root/must-input producer above. -/
theorem not_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (child : Circuit) :
    CheckedCircuitRejectCertificate sigma witness mode (.not child) := by
  intro hinvalid tail frames consumed padding hlen hread
  exact invalid_not_reaches_reject
    mode witness child tail frames consumed padding hinvalid

/-- Structural rejection producer for conjunction.

The child rejection certificates are the only recursive inputs.  If the root
mode itself forbids conjunction, rejection is immediate.  In CNF mode:
* an invalid left child is entered and rejected recursively;
* if the left child is valid but the right child is invalid, the already
  certified positive left run is used to reach the right child, which is then
  rejected recursively. -/
theorem and_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (left right : Circuit)
    (hleftReject :
      CheckedCircuitRejectCertificate sigma witness .cnf left)
    (hrightReject :
      CheckedCircuitRejectCertificate sigma witness .cnf right) :
    ∀ mode : SyntaxMode,
      CheckedCircuitRejectCertificate
        sigma witness mode (.and left right) := by
  intro mode hinvalid tail frames consumed padding hlen hread
  cases mode with
  | clause =>
      have hroot :
          tagAllowed .clause (circuitTag (.and left right)) = false := rfl
      obtain ⟨m, hrun⟩ :=
        root_disallowed_reaches_reject
          .clause witness (.and left right) tail frames
          consumed padding hroot
      let cfg : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 3)
              ((encodeCircuit (.and left right)).drop 3 ++ tail)
              (encodeEvalFrames frames) padding }
      exact ⟨m, cfg, by simpa [cfg] using hrun, rfl⟩
  | mustInput =>
      have hroot :
          tagAllowed .mustInput (circuitTag (.and left right)) = false := rfl
      obtain ⟨m, hrun⟩ :=
        root_disallowed_reaches_reject
          .mustInput witness (.and left right) tail frames
          consumed padding hroot
      let cfg : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 3)
              ((encodeCircuit (.and left right)).drop 3 ++ tail)
              (encodeEvalFrames frames) padding }
      exact ⟨m, cfg, by simpa [cfg] using hrun, rfl⟩
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

      have hinvalidRight :
          modeCheck .cnf left = true →
            modeCheck .cnf right = false := by
        intro hleftTrue
        rw [modeCheck_and] at hinvalid
        simpa [tagAllowed, hleftTrue] using hinvalid

      obtain ⟨m0, h0⟩ :=
        and_checked_reaches_need
          .cnf witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding (by rfl)

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
          obtain ⟨m1, cfgReject, h1, hrej⟩ :=
            hleftReject hleftMode
              (encodeCircuit right ++ tail) (.andLeft :: frames)
              (consumed + 3) padLeft hlenLeft hreadLeft

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

          exact ⟨m0 + m1, cfgReject, hAll, hrej⟩

      | true =>
          have hrightMode : modeCheck .cnf right = false :=
            hinvalidRight hleftMode

          have hleftPositive :=
            P01CheckedEvalRunCircuitCertificate.circuit_certificate
              sigma witness left .cnf

          obtain ⟨m1, cfgLeft, h1, hout1⟩ :=
            hleftPositive hleftMode
              (encodeCircuit right ++ tail) (.andLeft :: frames)
              (consumed + 3) padLeft hlenLeft hreadLeft

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

          have hRightTail : encodeCircuit right ++ tail ≠ [] := by
            intro hnil
            have henc : encodeCircuit right = [] :=
              (List.append_eq_nil.mp hnil).1
            exact P01EvalRunCircuitCertificate.encodeCircuit_ne_nil right henc

          obtain ⟨consumed1, padding1, hcfgLeft⟩ :=
            outcome_have_of_tail_ne_nil
              witness (exitMode .cnf left) (evalCircuit sigma left)
              (encodeCircuit right ++ tail) (.andLeft :: frames)
              cfgLeft hRightTail hout1
          subst cfgLeft

          obtain ⟨m2, hm2, h2⟩ :=
            andLeftReturn_checked_reaches_need
              (exitMode .cnf left)
              witness (encodeCircuit right ++ tail)
              (encodeEvalFrames frames)
              consumed1 padding1 (evalCircuit sigma left)

          let padRight := (((padding1 + 3) - 1) - 1) - 1
          let cNeedRight : CheckedConfig :=
            { state := .need .cnf needExprCompositeMachine.initial,
              tape :=
                evalCursorStackEndTape witness consumed1
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
                       evalCursorStackEndTape witness consumed1
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
                   evalCursorStackEndTape witness consumed1
                     (encodeCircuit right ++ tail)
                     (encodeEvalFrames (.andLeft :: frames))
                     padding1 } : CheckedConfig)
              cNeedRight h01 h2'

          obtain ⟨m3, cfgReject, h3, hrej⟩ :=
            hrightReject hrightMode tail
              (.andRight (evalCircuit sigma left) :: frames)
              consumed1 padRight hlenRight hreadRight

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

          exact ⟨m0 + m1 + m2 + m3, cfgReject, hAll, hrej⟩

#print axioms MCore.Real.P01CheckedEvalReject.and_reject_certificate

/-- Structural rejection producer for disjunction.

If the root OR tag is forbidden by the current mode, rejection is immediate.
Otherwise both children are checked in clause mode; the first invalid child
rejects recursively, and a valid left child is physically evaluated before
entering a rejecting right child. -/
theorem or_reject_certificate
    (sigma : Assignment)
    (witness : BitString)
    (left right : Circuit)
    (hleftReject :
      CheckedCircuitRejectCertificate sigma witness .clause left)
    (hrightReject :
      CheckedCircuitRejectCertificate sigma witness .clause right) :
    ∀ mode : SyntaxMode,
      CheckedCircuitRejectCertificate
        sigma witness mode (.or left right) := by
  intro mode hinvalid tail frames consumed padding hlen hread
  cases hroot : tagAllowed mode .or with
  | false =>
      obtain ⟨m, hrun⟩ :=
        root_disallowed_reaches_reject
          mode witness (.or left right) tail frames
          consumed padding (by
            simpa [circuitTag] using hroot)
      let cfg : CheckedConfig :=
        { state := .reject,
          tape :=
            evalCursorReadTape witness (consumed + 3)
              ((encodeCircuit (.or left right)).drop 3 ++ tail)
              (encodeEvalFrames frames) padding }
      exact ⟨m, cfg, by simpa [cfg] using hrun, rfl⟩
  | true =>
      have hinvalidRight :
          modeCheck .clause left = true →
            modeCheck .clause right = false := by
        intro hleftTrue
        rw [modeCheck_or] at hinvalid
        simpa [hroot, hleftTrue] using hinvalid

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

      obtain ⟨m0, h0⟩ :=
        or_checked_reaches_need
          mode witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding (by
            simpa using hroot)

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
        simpa [cNeedLeft, padLeft, encodeCircuit,
          childMode, List.append_assoc] using h0

      cases hleftMode : modeCheck .clause left with
      | false =>
          obtain ⟨m1, cfgReject, h1, hrej⟩ :=
            hleftReject hleftMode
              (encodeCircuit right ++ tail) (.orLeft :: frames)
              (consumed + 3) padLeft hlenLeft hreadLeft

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

          exact ⟨m0 + m1, cfgReject, hAll, hrej⟩

      | true =>
          have hrightMode : modeCheck .clause right = false :=
            hinvalidRight hleftMode

          have hleftPositive :=
            P01CheckedEvalRunCircuitCertificate.circuit_certificate
              sigma witness left .clause

          obtain ⟨m1, cfgLeft, h1, hout1⟩ :=
            hleftPositive hleftMode
              (encodeCircuit right ++ tail) (.orLeft :: frames)
              (consumed + 3) padLeft hlenLeft hreadLeft

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

          have hRightTail : encodeCircuit right ++ tail ≠ [] := by
            intro hnil
            have henc : encodeCircuit right = [] :=
              (List.append_eq_nil_iff.mp hnil).1
            exact P01EvalRunCircuitCertificate.encodeCircuit_ne_nil right henc

          obtain ⟨consumed1, padding1, hcfgLeft⟩ :=
            outcome_have_of_tail_ne_nil
              witness (exitMode .clause left) (evalCircuit sigma left)
              (encodeCircuit right ++ tail) (.orLeft :: frames)
              cfgLeft hRightTail hout1
          subst cfgLeft

          obtain ⟨m2, hm2, h2⟩ :=
            orLeftReturn_checked_reaches_need
              (exitMode .clause left)
              witness (encodeCircuit right ++ tail)
              (encodeEvalFrames frames)
              consumed1 padding1 (evalCircuit sigma left)

          let padRight := (((padding1 + 3) - 1) - 1) - 1
          let cNeedRight : CheckedConfig :=
            { state := .need .clause needExprCompositeMachine.initial,
              tape :=
                evalCursorStackEndTape witness consumed1
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
                       evalCursorStackEndTape witness consumed1
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
                   evalCursorStackEndTape witness consumed1
                     (encodeCircuit right ++ tail)
                     (encodeEvalFrames (.orLeft :: frames))
                     padding1 } : CheckedConfig)
              cNeedRight h01 h2'

          obtain ⟨m3, cfgReject, h3, hrej⟩ :=
            hrightReject hrightMode tail
              (.orRight (evalCircuit sigma left) :: frames)
              consumed1 padRight hlenRight hreadRight

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

          exact ⟨m0 + m1 + m2 + m3, cfgReject, hAll, hrej⟩

#print axioms MCore.Real.P01CheckedEvalReject.or_reject_certificate


#print axioms MCore.Real.P01CheckedEvalReject.input_reject_certificate
#print axioms MCore.Real.P01CheckedEvalReject.const_reject_certificate
#print axioms MCore.Real.P01CheckedEvalReject.not_reject_certificate

#print axioms MCore.Real.P01CheckedEvalReject.mustInput_root_disallowed_of_check_false
#print axioms MCore.Real.P01CheckedEvalReject.invalid_not_reaches_reject

#print axioms MCore.Real.P01CheckedEvalReject.root_disallowed_reaches_reject

end P01CheckedEvalReject
end Real
end MCore
