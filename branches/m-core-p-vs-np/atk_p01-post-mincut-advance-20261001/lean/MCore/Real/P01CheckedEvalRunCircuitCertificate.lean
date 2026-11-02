import MCore.Real.P01EvalRunCircuitCertificate
import MCore.Real.CanonicalCircuitBits
import MCore.Real.CanonicalSATWitness
import MCore.Real.P01EncodedFrameTape
import MCore.Real.P01CheckedEvalRunBaseCases
import MCore.Real.P01CheckedEvalRunNeedTags
import MCore.Real.P01CheckedEvalRunHaveValue
import MCore.Real.P01CheckedEvalRunInputTag
import MCore.Real.CanonicalSATWitness
import MCore.Real.CanonicalCircuitBits
import MCore.Real.P01EncodedFrameTape

namespace MCore
namespace Real
namespace P01CheckedEvalRunCircuitCertificate

open CanonicalFinalProof
open CircuitK1
open CanonicalSATWitness
open CanonicalCircuitBits
open P01EncodedFrameTape
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunNeedTags
open P01CheckedEvalRunHaveValue
open P01CheckedEvalRunInputTag
open P01CNFMode
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Normalize a checked haveValue state into the external checked circuit
outcome.  If external source or continuation frames remain, no step is needed.
If both are empty, reuse the mandatory source-empty finalization guard. -/
theorem have_reaches_outcome
    (mode : SyntaxMode)
    (witness : BitString)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat) :
    ∃ m cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start value),
             tape :=
               evalCursorStackEndTape witness consumed tail
                 (P01EncodedFrameTape.encodeEvalFrames frames) padding }] ∧
      CheckedLoopOutcome witness mode value tail frames cfg := by
  cases tail with
  | cons b bs =>
      let cfg : CheckedConfig :=
        { state := .have mode (.start value),
          tape :=
            evalCursorStackEndTape witness consumed (b :: bs)
              (P01EncodedFrameTape.encodeEvalFrames frames) padding }
      refine ⟨0, cfg, ?_, ?_⟩
      · simp [cfg, NTM.runBranches]
      · exact ⟨consumed, padding, rfl⟩
  | nil =>
      cases frames with
      | cons f fs =>
          let cfg : CheckedConfig :=
            { state := .have mode (.start value),
              tape :=
                evalCursorStackEndTape witness consumed []
                  (P01EncodedFrameTape.encodeEvalFrames (f :: fs)) padding }
          refine ⟨0, cfg, ?_, ?_⟩
          · simp [cfg, NTM.runBranches]
          · exact ⟨consumed, padding, rfl⟩
      | nil =>
          obtain ⟨m, hm, hrun⟩ :=
            checked_empty_frames_reaches_final
              mode witness consumed padding value
          let cfg : CheckedConfig :=
            { state := .final value,
              tape :=
                Tape.move none .left
                  (Tape.move none .left
                    (evalCursorStackEndTape witness consumed [] [] padding)) }
          refine ⟨m, cfg, ?_, ?_⟩
          · simpa [cfg] using hrun
          · exact ⟨cfg.tape, rfl⟩

/-- Checked structural producer for negation.

A checked negation is necessarily a literal: `modeCheck_not` forces its child
into `mustInput`.  The physical route therefore consists of the admitted neg
tag, the already-certified checked child run, the neg continuation return, and
the common haveValue normalization above. -/
theorem neg_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (circuit : Circuit)
    (hchild :
      CheckedCircuitRunCertificate
        sigma witness (childMode mode .neg) circuit) :
    CheckedCircuitRunCertificate sigma witness mode (.not circuit) := by
  intro hmode tail frames consumed padding hlen hread

  have hmodeParts :
      tagAllowed mode .neg = true ∧
        modeCheck (childMode mode .neg) circuit = true := by
    have h := hmode
    rw [modeCheck_not] at h
    simpa using h
  have hAllowed : tagAllowed mode .neg = true := hmodeParts.1
  have hchildMode :
      modeCheck (childMode mode .neg) circuit = true := hmodeParts.2

  have hlenChild : CanonicalSATWitness.varBound circuit ≤ witness.length := by
    simpa [CanonicalSATWitness.varBound] using hlen
  have hreadChild :
      ∀ i, i < CanonicalSATWitness.varBound circuit →
        witness.getD i false = sigma i := by
    intro i hi
    exact hread i (by simpa [CanonicalSATWitness.varBound] using hi)

  obtain ⟨m0, h0⟩ :=
    neg_checked_reaches_need
      mode witness (CanonicalCircuitBits.encodeCircuit circuit ++ tail)
        (P01EncodedFrameTape.encodeEvalFrames frames) consumed padding hAllowed

  let padChild := ((padding - 1) - 1) - 1
  let childMode' := childMode mode .neg
  let cNeed : CheckedConfig :=
    { state := .need childMode' needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          (CanonicalCircuitBits.encodeCircuit circuit ++ tail)
          (P01EncodedFrameTape.encodeEvalFrame .neg ++ P01EncodedFrameTape.encodeEvalFrames frames)
          padChild }

  have h0' :
      cNeed ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (CanonicalCircuitBits.encodeCircuit (.not circuit) ++ tail)
                 (P01EncodedFrameTape.encodeEvalFrames frames) padding }] := by
    simpa [cNeed, childMode', childMode, padChild, CanonicalCircuitBits.encodeCircuit,
      List.append_assoc] using h0

  obtain ⟨m1, cfg1, h1, hout1⟩ :=
    hchild hchildMode tail (.neg :: frames)
      (consumed + 3) padChild hlenChild hreadChild

  have h1' :
      cfg1 ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeed] := by
    simpa [cNeed, childMode', P01EncodedFrameTape.encodeEvalFrames,
      List.append_assoc] using h1

  have h01 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 m1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (CanonicalCircuitBits.encodeCircuit (.not circuit) ++ tail)
             (P01EncodedFrameTape.encodeEvalFrames frames) padding }]
      cNeed cfg1 h0' h1'

  have hchildInput :
      ∃ i, circuit = .input i := by
    have hm :
        modeCheck .mustInput circuit = true := by
      simpa [childMode] using hchildMode
    exact (modeCheck_mustInput_iff circuit).1 hm

  have houtHave :
      ∃ consumed1 padding1,
        cfg1 =
          { state := .have .mustInput (.start (evalCircuit sigma circuit)),
            tape :=
              evalCursorStackEndTape witness consumed1 tail
                (P01EncodedFrameTape.encodeEvalFrames (.neg :: frames)) padding1 } := by
    rcases hchildInput with ⟨i, rfl⟩
    simpa [CheckedLoopOutcome, exitMode, childMode, circuitTag] using hout1

  rcases houtHave with ⟨consumed1, padding1, hcfg1⟩
  subst cfg1

  obtain ⟨m2, hm2, h2⟩ :=
    negReturn_checked_reaches_have
      .mustInput witness tail (P01EncodedFrameTape.encodeEvalFrames frames)
      consumed1 padding1 (evalCircuit sigma circuit)

  let cHave : CheckedConfig :=
    { state := .have .mustInput (.start (!(evalCircuit sigma circuit))),
      tape :=
        evalCursorStackEndTape witness consumed1 tail
          (P01EncodedFrameTape.encodeEvalFrames frames) (padding1 + 3) }

  have h2' :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches m2
          [{ state := .have .mustInput
               (.start (evalCircuit sigma circuit)),
             tape :=
               evalCursorStackEndTape witness consumed1 tail
                 (P01EncodedFrameTape.encodeEvalFrames (.neg :: frames)) padding1 }] := by
    simpa [cHave, P01EncodedFrameTape.encodeEvalFrames, List.append_assoc] using h2

  have h012 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1) m2
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (CanonicalCircuitBits.encodeCircuit (.not circuit) ++ tail)
             (P01EncodedFrameTape.encodeEvalFrames frames) padding }]
      ({ state := .have .mustInput
           (.start (evalCircuit sigma circuit)),
         tape :=
           evalCursorStackEndTape witness consumed1 tail
             (P01EncodedFrameTape.encodeEvalFrames (.neg :: frames)) padding1 } : CheckedConfig)
      cHave h01 h2'

  obtain ⟨m3, cfgFinal, h3, hout3⟩ :=
    have_reaches_outcome
      .mustInput witness (!(evalCircuit sigma circuit))
      tail frames consumed1 (padding1 + 3)

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1 + m2) m3
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (CanonicalCircuitBits.encodeCircuit (.not circuit) ++ tail)
             (P01EncodedFrameTape.encodeEvalFrames frames) padding }]
      cHave cfgFinal h012 h3

  refine ⟨m0 + m1 + m2 + m3, cfgFinal, hAll, ?_⟩
  simpa [CheckedLoopOutcome, exitMode, childMode, circuitTag, evalCircuit] using hout3

/-- A checked outcome with a nonempty unread source is necessarily a
physical haveValue state; the global final branch is impossible. -/
theorem outcome_have_of_tail_ne_nil
    (witness : BitString)
    (mode : SyntaxMode)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (cfg : CheckedConfig)
    (hne : tail ≠ [])
    (h : CheckedLoopOutcome witness mode value tail frames cfg) :
    ∃ consumed padding,
      cfg =
        { state := .have mode (.start value),
          tape :=
            evalCursorStackEndTape witness consumed tail
              (P01EncodedFrameTape.encodeEvalFrames frames) padding } := by
  cases tail with
  | nil =>
      exact False.elim (hne rfl)
  | cons b bs =>
      exact h

/-- A checked outcome with a nonempty continuation stack is necessarily a
physical haveValue state, even when the unread source tail is empty. -/
theorem outcome_have_of_frames_ne_nil
    (witness : BitString)
    (mode : SyntaxMode)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (cfg : CheckedConfig)
    (hne : frames ≠ [])
    (h : CheckedLoopOutcome witness mode value tail frames cfg) :
    ∃ consumed padding,
      cfg =
        { state := .have mode (.start value),
          tape :=
            evalCursorStackEndTape witness consumed tail
              (P01EncodedFrameTape.encodeEvalFrames frames) padding } := by
  cases tail with
  | cons b bs =>
      exact h
  | nil =>
      cases frames with
      | nil =>
          exact False.elim (hne rfl)
      | cons f fs =>
          exact h

/-- Checked structural producer for conjunction.  A valid conjunction can
only occur in CNF mode; both children are recursively checked in CNF mode. -/
theorem and_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (left right : Circuit)
    (hleft : CheckedCircuitRunCertificate sigma witness .cnf left)
    (hright : CheckedCircuitRunCertificate sigma witness .cnf right) :
    CheckedCircuitRunCertificate sigma witness mode (.and left right) := by
  intro hmode tail frames consumed padding hlen hread
  cases mode with
  | clause =>
      rw [modeCheck_and] at hmode
      simp [tagAllowed] at hmode
  | mustInput =>
      rw [modeCheck_and] at hmode
      simp [tagAllowed] at hmode
  | cnf =>
      have hchildren :
          modeCheck .cnf left = true ∧ modeCheck .cnf right = true := by
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

      obtain ⟨m1, cfgLeft, h1, hout1⟩ :=
        hleft hleftMode
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

      obtain ⟨m3, cfgRight, h3, hout3⟩ :=
        hright hrightMode tail
          (.andRight (evalCircuit sigma left) :: frames)
          consumed1 padRight hlenRight hreadRight

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

      obtain ⟨consumed2, padding2, hcfgRight⟩ :=
        outcome_have_of_frames_ne_nil
          witness (exitMode .cnf right) (evalCircuit sigma right)
          tail (.andRight (evalCircuit sigma left) :: frames)
          cfgRight (by simp) hout3
      subst cfgRight

      obtain ⟨m4, hm4, h4⟩ :=
        andRightReturn_checked_reaches_have
          (exitMode .cnf right)
          witness tail (encodeEvalFrames frames)
          consumed2 padding2
          (evalCircuit sigma left) (evalCircuit sigma right)

      let finalValue :=
        Bool.and (evalCircuit sigma left) (evalCircuit sigma right)
      let cHave : CheckedConfig :=
        { state := .have .cnf (.start finalValue),
          tape :=
            evalCursorStackEndTape witness consumed2 tail
              (encodeEvalFrames frames) (padding2 + 3) }

      have h4' :
          cHave ∈
            checkedEvalRunLoopMachine.runBranches m4
              [{ state := .have (exitMode .cnf right)
                   (.start (evalCircuit sigma right)),
                 tape :=
                   evalCursorStackEndTape witness consumed2 tail
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
               evalCursorStackEndTape witness consumed2 tail
                 (encodeEvalFrames
                   (.andRight (evalCircuit sigma left) :: frames))
                 padding2 } : CheckedConfig)
          cHave h0123 h4'

      obtain ⟨m5, cfgFinal, h5, hout5⟩ :=
        have_reaches_outcome
          .cnf witness finalValue tail frames
          consumed2 (padding2 + 3)

      have hAll :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          (m0 + m1 + m2 + m3 + m4) m5
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.and left right) ++ tail)
                 (encodeEvalFrames frames) padding }]
          cHave cfgFinal h01234 h5

      refine ⟨m0 + m1 + m2 + m3 + m4 + m5, cfgFinal, hAll, ?_⟩
      simpa [finalValue, CheckedLoopOutcome, exitMode, childMode,
        circuitTag, evalCircuit] using hout5

/-- Checked structural producer for disjunction.  A valid disjunction may
occur in CNF or clause mode, but both children are recursively checked in
clause mode and the post-frame mode is clause. -/
theorem or_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (left right : Circuit)
    (hleft : CheckedCircuitRunCertificate sigma witness .clause left)
    (hright : CheckedCircuitRunCertificate sigma witness .clause right) :
    CheckedCircuitRunCertificate sigma witness mode (.or left right) := by
  intro hmode tail frames consumed padding hlen hread

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
      (encodeEvalFrames frames) consumed padding hAllowed

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

  obtain ⟨m1, cfgLeft, h1, hout1⟩ :=
    hleft hleftMode
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

  obtain ⟨m3, cfgRight, h3, hout3⟩ :=
    hright hrightMode tail
      (.orRight (evalCircuit sigma left) :: frames)
      consumed1 padRight hlenRight hreadRight

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

  obtain ⟨consumed2, padding2, hcfgRight⟩ :=
    outcome_have_of_frames_ne_nil
      witness (exitMode .clause right) (evalCircuit sigma right)
      tail (.orRight (evalCircuit sigma left) :: frames)
      cfgRight (by simp) hout3
  subst cfgRight

  obtain ⟨m4, hm4, h4⟩ :=
    orRightReturn_checked_reaches_have
      (exitMode .clause right)
      witness tail (encodeEvalFrames frames)
      consumed2 padding2
      (evalCircuit sigma left) (evalCircuit sigma right)

  let finalValue :=
    Bool.or (evalCircuit sigma left) (evalCircuit sigma right)
  let cHave : CheckedConfig :=
    { state := .have .clause (.start finalValue),
      tape :=
        evalCursorStackEndTape witness consumed2 tail
          (encodeEvalFrames frames) (padding2 + 3) }

  have h4' :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches m4
          [{ state := .have (exitMode .clause right)
               (.start (evalCircuit sigma right)),
             tape :=
               evalCursorStackEndTape witness consumed2 tail
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
           evalCursorStackEndTape witness consumed2 tail
             (encodeEvalFrames
               (.orRight (evalCircuit sigma left) :: frames))
             padding2 } : CheckedConfig)
      cHave h0123 h4'

  obtain ⟨m5, cfgFinal, h5, hout5⟩ :=
    have_reaches_outcome
      .clause witness finalValue tail frames
      consumed2 (padding2 + 3)

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1 + m2 + m3 + m4) m5
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cHave cfgFinal h01234 h5

  refine ⟨m0 + m1 + m2 + m3 + m4 + m5, cfgFinal, hAll, ?_⟩
  simpa [finalValue, CheckedLoopOutcome, exitMode, childMode,
    circuitTag, evalCircuit] using hout5

/-- Structural producer for every checked circuit.

This theorem contains no new physical machine.  It closes the syntax recursion
by composing the already-certified producers for input, constants, negation,
conjunction, and disjunction. -/
theorem circuit_certificate
    (sigma : Assignment)
    (witness : BitString) :
    ∀ (phi : Circuit) (mode : SyntaxMode),
      CheckedCircuitRunCertificate sigma witness mode phi := by
  intro phi
  induction phi with
  | input i =>
      intro mode
      exact P01CheckedEvalRunInputTag.input_certificate
        sigma witness mode i
  | const v =>
      intro mode
      exact P01CheckedEvalRunBaseCases.const_certificate
        sigma witness mode v
  | not child ih =>
      intro mode
      exact neg_certificate
        sigma witness mode child
        (ih (childMode mode .neg))
  | and left right ihLeft ihRight =>
      intro mode
      exact and_certificate
        sigma witness mode left right
        (ihLeft .cnf) (ihRight .cnf)
  | or left right ihLeft ihRight =>
      intro mode
      exact or_certificate
        sigma witness mode left right
        (ihLeft .clause) (ihRight .clause)

#print axioms MCore.Real.P01CheckedEvalRunCircuitCertificate.circuit_certificate

#print axioms MCore.Real.P01CheckedEvalRunCircuitCertificate.or_certificate

#print axioms MCore.Real.P01CheckedEvalRunCircuitCertificate.and_certificate

#print axioms MCore.Real.P01CheckedEvalRunCircuitCertificate.outcome_have_of_tail_ne_nil
#print axioms MCore.Real.P01CheckedEvalRunCircuitCertificate.outcome_have_of_frames_ne_nil

#print axioms MCore.Real.P01CheckedEvalRunCircuitCertificate.have_reaches_outcome
#print axioms MCore.Real.P01CheckedEvalRunCircuitCertificate.neg_certificate

end P01CheckedEvalRunCircuitCertificate
end Real
end MCore
