import MCore.Real.P01EvalRunLoopRun
import MCore.Real.P01EvalRunInputTag
import MCore.Real.P01EvalRunHaveValue
import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace P01EvalRunCircuitCertificate

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
open P01InputNodeCompositeRun
open P01InputNodeRoundTrip

abbrev LoopConfig :=
  Configuration EvalRunLoopState (Option Bool)

/-- Normalized physical result after evaluating one encoded circuit while
preserving an arbitrary external tail/continuation.

When no external work remains, the loop is already in its global final state.
Otherwise it is normalized to the canonical `haveValue` restart state. -/
def LoopOutcome
    (witness : BitString)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (cfg : LoopConfig) : Prop :=
  match tail, frames with
  | [], [] =>
      ∃ tape : Tape (Option Bool),
        cfg = { state := .final value, tape := tape }
  | _, _ =>
      ∃ consumed padding : Nat,
        cfg =
          { state := .have (.start value),
            tape :=
              evalCursorStackEndTape witness consumed tail
                (encodeEvalFrames frames) padding }

/-- Producer-first certificate for one circuit: starting from the canonical
physical `needExpr` representation of `encodeCircuit phi ++ tail`, the
global loop reaches the exact semantic value while preserving the external
tail and continuation shape.

No complexity bound is claimed yet; this is the semantic/run certificate that
will later receive the polynomial majorant. -/
def CircuitRunCertificate
    (sigma : Assignment)
    (witness : BitString)
    (phi : Circuit) : Prop :=
  ∀ (tail : BitString) (frames : List EvalFrame)
      (consumed padding : Nat),
    varBound phi ≤ witness.length →
    (∀ i, i < varBound phi →
      witness.getD i false = sigma i) →
    ∃ m cfg,
      cfg ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit phi ++ tail)
                 (encodeEvalFrames frames) padding }] ∧
      LoopOutcome witness (evalCircuit sigma phi) tail frames cfg

/-- Input nodes inhabit the global circuit-run certificate directly from the
already-certified indexed-input loop. -/
theorem input_certificate
    (sigma : Assignment)
    (witness : BitString)
    (i : Nat) :
    CircuitRunCertificate sigma witness (.input i) := by
  intro tail frames consumed padding hlen hread
  have hiVar : i < varBound (.input i) := by
    simp [varBound]
  have hi : i < witness.length :=
    Nat.lt_of_lt_of_le hiVar hlen
  have hvalue : witness.getD i false = sigma i :=
    hread i hiVar
  obtain ⟨m, hm, hrun⟩ :=
    inputTag_loop_reaches_mode
      witness tail (encodeEvalFrames frames)
      consumed padding i hi
  let cfg : LoopConfig :=
    inputLoopConfig
      ({ state :=
           .done (witness.getD i false)
             (inputNodeFinalMode tail (encodeEvalFrames frames)),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex (consumed + 3) i)
             tail (encodeEvalFrames frames) padding).tape } :
        Configuration P01InputNodeCompositeNTM.InputNodeCompositeState
          (Option Bool))
  refine ⟨m, cfg, ?_, ?_⟩
  · simpa [cfg, encodeCircuit] using hrun
  · change LoopOutcome witness (sigma i) tail frames cfg
    rw [← hvalue]
    cases tail with
    | cons b bs =>
        refine ⟨consumedAfterInputIndex (consumed + 3) i, padding, ?_⟩
        simp [LoopOutcome, cfg, inputLoopConfig, inputLoopEmbed,
          inputNodeFinalMode, inputAfterReadTarget]
    | nil =>
        cases frames with
        | nil =>
            refine ⟨(inputAfterReadTarget witness
              (consumedAfterInputIndex (consumed + 3) i)
              [] [] padding).tape, ?_⟩
            simp [LoopOutcome, cfg, inputLoopConfig, inputLoopEmbed,
              inputNodeFinalMode, inputAfterReadTarget]
        | cons f fs =>
            refine ⟨consumedAfterInputIndex (consumed + 3) i, padding, ?_⟩
            cases f with
            | neg =>
                simp [LoopOutcome, cfg, inputLoopConfig, inputLoopEmbed,
                  inputNodeFinalMode, inputAfterReadTarget,
                  encodeEvalFrames, encodeEvalFrame]
            | andLeft =>
                simp [LoopOutcome, cfg, inputLoopConfig, inputLoopEmbed,
                  inputNodeFinalMode, inputAfterReadTarget,
                  encodeEvalFrames, encodeEvalFrame]
            | andRight b =>
                cases b <;>
                  simp [LoopOutcome, cfg, inputLoopConfig, inputLoopEmbed,
                    inputNodeFinalMode, inputAfterReadTarget,
                    encodeEvalFrames, encodeEvalFrame]
            | orLeft =>
                simp [LoopOutcome, cfg, inputLoopConfig, inputLoopEmbed,
                  inputNodeFinalMode, inputAfterReadTarget,
                  encodeEvalFrames, encodeEvalFrame]
            | orRight b =>
                cases b <;>
                  simp [LoopOutcome, cfg, inputLoopConfig, inputLoopEmbed,
                    inputNodeFinalMode, inputAfterReadTarget,
                    encodeEvalFrames, encodeEvalFrame]

/-- Constant-false nodes inhabit the global circuit-run certificate. -/
theorem constFalse_certificate
    (sigma : Assignment)
    (witness : BitString) :
    CircuitRunCertificate sigma witness (.const false) := by
  intro tail frames consumed padding hlen hread
  obtain ⟨m1, hm1, h1⟩ :=
    constFalse_loop_reaches_have
      witness tail (encodeEvalFrames frames) consumed padding
  let cHave : LoopConfig :=
    { state := .have (.start false),
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          tail (encodeEvalFrames frames) padding }
  have h1' :
      cHave ∈
        evalRunLoopMachine.runBranches m1
          [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.const false) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cHave, encodeCircuit] using h1
  cases tail with
  | cons b bs =>
      refine ⟨m1, cHave, h1', ?_⟩
      exact ⟨consumed + 3, padding, rfl⟩
  | nil =>
      cases frames with
      | cons f fs =>
          refine ⟨m1, cHave, h1', ?_⟩
          exact ⟨consumed + 3, padding, rfl⟩
      | nil =>
          obtain ⟨m2, hm2, h2⟩ :=
            emptyFrames_loop_reaches_final
              witness [] (consumed + 3) padding false
          let cFinal : LoopConfig :=
            { state := .final false,
              tape :=
                evalCursorStackEndTape witness (consumed + 3)
                  [] [] padding }
          have hall :=
            mem_runBranches_trans evalRunLoopMachine
              m1 m2
              [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.const false))
                     [] padding }]
              cHave cFinal h1' h2
          refine ⟨m1 + m2, cFinal, ?_, ?_⟩
          · simpa using hall
          · exact ⟨cFinal.tape, rfl⟩

/-- Constant-true nodes inhabit the global circuit-run certificate. -/
theorem constTrue_certificate
    (sigma : Assignment)
    (witness : BitString) :
    CircuitRunCertificate sigma witness (.const true) := by
  intro tail frames consumed padding hlen hread
  obtain ⟨m1, hm1, h1⟩ :=
    constTrue_loop_reaches_have
      witness tail (encodeEvalFrames frames) consumed padding
  let cHave : LoopConfig :=
    { state := .have (.start true),
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          tail (encodeEvalFrames frames) padding }
  have h1' :
      cHave ∈
        evalRunLoopMachine.runBranches m1
          [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.const true) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cHave, encodeCircuit] using h1
  cases tail with
  | cons b bs =>
      refine ⟨m1, cHave, h1', ?_⟩
      exact ⟨consumed + 3, padding, rfl⟩
  | nil =>
      cases frames with
      | cons f fs =>
          refine ⟨m1, cHave, h1', ?_⟩
          exact ⟨consumed + 3, padding, rfl⟩
      | nil =>
          obtain ⟨m2, hm2, h2⟩ :=
            emptyFrames_loop_reaches_final
              witness [] (consumed + 3) padding true
          let cFinal : LoopConfig :=
            { state := .final true,
              tape :=
                evalCursorStackEndTape witness (consumed + 3)
                  [] [] padding }
          have hall :=
            mem_runBranches_trans evalRunLoopMachine
              m1 m2
              [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.const true))
                     [] padding }]
              cHave cFinal h1' h2
          refine ⟨m1 + m2, cFinal, ?_, ?_⟩
          · simpa using hall
          · exact ⟨cFinal.tape, rfl⟩

theorem const_certificate
    (sigma : Assignment)
    (witness : BitString)
    (b : Bool) :
    CircuitRunCertificate sigma witness (.const b) := by
  cases b
  · exact constFalse_certificate sigma witness
  · exact constTrue_certificate sigma witness





/-- Normalize an already-computed physical value into the circuit certificate's
external outcome. If external source/frames remain, zero additional steps are
needed; if both are empty, the existing haveValue loop closes to final. -/
theorem have_reaches_outcome
    (witness : BitString)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat) :
    ∃ m cfg,
      cfg ∈
        evalRunLoopMachine.runBranches m
          [{ state := .have (.start value),
             tape :=
               evalCursorStackEndTape witness consumed tail
                 (encodeEvalFrames frames) padding }] ∧
      LoopOutcome witness value tail frames cfg := by
  cases tail with
  | cons b bs =>
      let cHave : LoopConfig :=
        { state := .have (.start value),
          tape :=
            evalCursorStackEndTape witness consumed (b :: bs)
              (encodeEvalFrames frames) padding }
      refine ⟨0, cHave, ?_, ?_⟩
      · simp [NTM.runBranches, cHave]
      · exact ⟨consumed, padding, rfl⟩
  | nil =>
      cases frames with
      | cons f fs =>
          let cHave : LoopConfig :=
            { state := .have (.start value),
              tape :=
                evalCursorStackEndTape witness consumed []
                  (encodeEvalFrames (f :: fs)) padding }
          refine ⟨0, cHave, ?_, ?_⟩
          · simp [NTM.runBranches, cHave]
          · exact ⟨consumed, padding, rfl⟩
      | nil =>
          obtain ⟨m, hm, hrun⟩ :=
            emptyFrames_loop_reaches_final
              witness [] consumed padding value
          let cFinal : LoopConfig :=
            { state := .final value,
              tape :=
                evalCursorStackEndTape witness consumed [] [] padding }
          refine ⟨m, cFinal, ?_, ?_⟩
          · simpa [cFinal] using hrun
          · exact ⟨cFinal.tape, rfl⟩

#print axioms MCore.Real.P01EvalRunCircuitCertificate.have_reaches_outcome

/-- Structural producer for negation: execute the physical 011 tag, recurse on
the child under a neg continuation frame, then discharge that frame with the
already-certified physical haveValue loop. -/
theorem neg_certificate
    (sigma : Assignment)
    (witness : BitString)
    (circuit : Circuit)
    (hchild : CircuitRunCertificate sigma witness circuit) :
    CircuitRunCertificate sigma witness (.not circuit) := by
  intro tail frames consumed padding hlen hread
  have hlenChild : varBound circuit ≤ witness.length := by
    simpa [varBound] using hlen
  have hreadChild :
      ∀ i, i < varBound circuit →
        witness.getD i false = sigma i := by
    intro i hi
    exact hread i (by simpa [varBound] using hi)

  obtain ⟨m0, hm0, h0⟩ :=
    neg_loop_reaches_need
      witness (encodeCircuit circuit ++ tail)
      (encodeEvalFrames frames) consumed padding

  let padChild := ((padding - 1) - 1) - 1
  let cNeed : LoopConfig :=
    { state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          (encodeCircuit circuit ++ tail)
          (encodeEvalFrame .neg ++ encodeEvalFrames frames)
          padChild }

  have h0' :
      cNeed ∈
        evalRunLoopMachine.runBranches m0
          [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.not circuit) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cNeed, padChild, encodeCircuit, List.append_assoc] using h0

  obtain ⟨m1, cfg1, h1, hout1⟩ :=
    hchild tail (.neg :: frames) (consumed + 3) padChild
      hlenChild hreadChild

  have h1' :
      cfg1 ∈ evalRunLoopMachine.runBranches m1 [cNeed] := by
    simpa [cNeed, encodeEvalFrames, List.append_assoc] using h1

  have h01 :=
    mem_runBranches_trans evalRunLoopMachine
      m0 m1
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not circuit) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeed cfg1 h0' h1'

  have houtHave :
      ∃ consumed1 padding1,
        cfg1 =
          { state := .have (.start (evalCircuit sigma circuit)),
            tape :=
              evalCursorStackEndTape witness consumed1 tail
                (encodeEvalFrames (.neg :: frames)) padding1 } := by
    simpa [LoopOutcome] using hout1
  rcases houtHave with ⟨consumed1, padding1, hcfg1⟩
  subst cfg1

  obtain ⟨m2, hm2, h2⟩ :=
    negReturn_loop_reaches_have
      witness tail (encodeEvalFrames frames)
      consumed1 padding1 (evalCircuit sigma circuit)

  let cHave : LoopConfig :=
    { state := .have (.start (!(evalCircuit sigma circuit))),
      tape :=
        evalCursorStackEndTape witness consumed1 tail
          (encodeEvalFrames frames) (padding1 + 3) }

  have h2' :
      cHave ∈
        evalRunLoopMachine.runBranches m2
          [{ state := .have (.start (evalCircuit sigma circuit)),
             tape :=
               evalCursorStackEndTape witness consumed1 tail
                 (encodeEvalFrames (.neg :: frames)) padding1 }] := by
    simpa [cHave, encodeEvalFrames, List.append_assoc] using h2

  have h012 :=
    mem_runBranches_trans evalRunLoopMachine
      (m0 + m1) m2
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.not circuit) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have (.start (evalCircuit sigma circuit)),
         tape :=
           evalCursorStackEndTape witness consumed1 tail
             (encodeEvalFrames (.neg :: frames)) padding1 } : LoopConfig)
      cHave h01 h2'

  cases tail with
  | cons b bs =>
      refine ⟨m0 + m1 + m2, cHave, h012, ?_⟩
      change LoopOutcome witness (evalCircuit sigma (.not circuit))
        (b :: bs) frames cHave
      refine ⟨consumed1, padding1 + 3, ?_⟩
      simp [cHave, evalCircuit]
  | nil =>
      cases frames with
      | cons f fs =>
          refine ⟨m0 + m1 + m2, cHave, h012, ?_⟩
          change LoopOutcome witness (evalCircuit sigma (.not circuit))
            [] (f :: fs) cHave
          refine ⟨consumed1, padding1 + 3, ?_⟩
          simp [cHave, evalCircuit]
      | nil =>
          obtain ⟨m3, hm3, h3⟩ :=
            emptyFrames_loop_reaches_final
              witness [] consumed1 (padding1 + 3)
                (!(evalCircuit sigma circuit))
          let cFinal : LoopConfig :=
            { state := .final (!(evalCircuit sigma circuit)),
              tape :=
                evalCursorStackEndTape witness consumed1
                  [] [] (padding1 + 3) }
          have h012Final :
              cHave ∈
                evalRunLoopMachine.runBranches (m0 + m1 + m2)
                  [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness consumed
                         (encodeCircuit (.not circuit))
                         [] padding }] := by
            simpa using h012
          have hAll :=
            mem_runBranches_trans evalRunLoopMachine
              (m0 + m1 + m2) m3
              [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.not circuit))
                     [] padding }]
              cHave cFinal h012Final h3
          refine ⟨m0 + m1 + m2 + m3, cFinal, ?_, ?_⟩
          · simpa using hAll
          · change LoopOutcome witness
              (evalCircuit sigma (.not circuit)) [] [] cFinal
            refine ⟨cFinal.tape, ?_⟩
            simp [cFinal, evalCircuit]



/-- Every canonical circuit encoding contains at least its three-bit tag. -/
theorem encodeCircuit_ne_nil
    (circuit : Circuit) :
    encodeCircuit circuit ≠ [] := by
  cases circuit with
  | input i =>
      simp [encodeCircuit]
  | const b =>
      cases b <;> simp [encodeCircuit]
  | not c =>
      simp [encodeCircuit]
  | and a b =>
      simp [encodeCircuit]
  | or a b =>
      simp [encodeCircuit]

/-- Structural producer for conjunction. The physical loop evaluates the left
child under an andLeft frame, converts that frame to andRight carrying the
left value, evaluates the right child, combines both Booleans, and normalizes
the resulting haveValue state into the external circuit outcome. -/
theorem and_certificate
    (sigma : Assignment)
    (witness : BitString)
    (left right : Circuit)
    (hleft : CircuitRunCertificate sigma witness left)
    (hright : CircuitRunCertificate sigma witness right) :
    CircuitRunCertificate sigma witness (.and left right) := by
  intro tail frames consumed padding hlen hread

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

  obtain ⟨m0, hm0, h0⟩ :=
    and_loop_reaches_need
      witness
      (encodeCircuit left ++ encodeCircuit right ++ tail)
      (encodeEvalFrames frames) consumed padding

  let padLeft := ((padding - 1) - 1) - 1
  let cNeedLeft : LoopConfig :=
    { state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrame .andLeft ++ encodeEvalFrames frames)
          padLeft }

  have h0' :
      cNeedLeft ∈
        evalRunLoopMachine.runBranches m0
          [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.and left right) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cNeedLeft, padLeft, encodeCircuit, List.append_assoc] using h0

  obtain ⟨m1, cfgLeft, h1, hout1⟩ :=
    hleft (encodeCircuit right ++ tail) (.andLeft :: frames)
      (consumed + 3) padLeft hlenLeft hreadLeft

  have h1' :
      cfgLeft ∈ evalRunLoopMachine.runBranches m1 [cNeedLeft] := by
    simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1

  have h01 :=
    mem_runBranches_trans evalRunLoopMachine
      m0 m1
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.and left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeedLeft cfgLeft h0' h1'

  have hRightTail :
      encodeCircuit right ++ tail ≠ [] := by
    intro hnil
    have henc : encodeCircuit right = [] := by
      exact (List.append_eq_nil.mp hnil).1
    exact encodeCircuit_ne_nil right henc

  have houtLeftHave :
      ∃ consumed1 padding1,
        cfgLeft =
          { state := .have (.start (evalCircuit sigma left)),
            tape :=
              evalCursorStackEndTape witness consumed1
                (encodeCircuit right ++ tail)
                (encodeEvalFrames (.andLeft :: frames))
                padding1 } := by
    cases htail : encodeCircuit right ++ tail with
    | nil =>
        exact False.elim (hRightTail htail)
    | cons b bs =>
        have htmp :
            ∃ consumed1 padding1,
              cfgLeft =
                { state := .have (.start (evalCircuit sigma left)),
                  tape :=
                    evalCursorStackEndTape witness consumed1
                      (b :: bs)
                      (encodeEvalFrames (.andLeft :: frames))
                      padding1 } := by
          simpa [LoopOutcome, htail] using hout1
        rcases htmp with ⟨consumed1, padding1, hcfg⟩
        refine ⟨consumed1, padding1, ?_⟩
        simpa [htail] using hcfg

  rcases houtLeftHave with ⟨consumed1, padding1, hcfgLeft⟩
  subst cfgLeft

  obtain ⟨m2, hm2, h2⟩ :=
    andLeftReturn_loop_reaches_need
      witness (encodeCircuit right ++ tail)
      (encodeEvalFrames frames)
      consumed1 padding1 (evalCircuit sigma left)

  let padRight := (((padding1 + 3) - 1) - 1) - 1
  let cNeedRight : LoopConfig :=
    { state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness consumed1
          (encodeCircuit right ++ tail)
          (encodeEvalFrame (.andRight (evalCircuit sigma left)) ++
            encodeEvalFrames frames)
          padRight }

  have h2' :
      cNeedRight ∈
        evalRunLoopMachine.runBranches m2
          [{ state := .have (.start (evalCircuit sigma left)),
             tape :=
               evalCursorStackEndTape witness consumed1
                 (encodeCircuit right ++ tail)
                 (encodeEvalFrames (.andLeft :: frames))
                 padding1 }] := by
    simpa [cNeedRight, padRight, encodeEvalFrames, List.append_assoc] using h2

  have h012 :=
    mem_runBranches_trans evalRunLoopMachine
      (m0 + m1) m2
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.and left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have (.start (evalCircuit sigma left)),
         tape :=
           evalCursorStackEndTape witness consumed1
             (encodeCircuit right ++ tail)
             (encodeEvalFrames (.andLeft :: frames))
             padding1 } : LoopConfig)
      cNeedRight h01 h2'

  obtain ⟨m3, cfgRight, h3, hout3⟩ :=
    hright tail (.andRight (evalCircuit sigma left) :: frames)
      consumed1 padRight hlenRight hreadRight

  have h3' :
      cfgRight ∈
        evalRunLoopMachine.runBranches m3 [cNeedRight] := by
    simpa [cNeedRight, encodeEvalFrames, List.append_assoc] using h3

  have h0123 :=
    mem_runBranches_trans evalRunLoopMachine
      (m0 + m1 + m2) m3
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.and left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeedRight cfgRight h012 h3'

  have houtRightHave :
      ∃ consumed2 padding2,
        cfgRight =
          { state := .have (.start (evalCircuit sigma right)),
            tape :=
              evalCursorStackEndTape witness consumed2 tail
                (encodeEvalFrames
                  (.andRight (evalCircuit sigma left) :: frames))
                padding2 } := by
    simpa [LoopOutcome] using hout3

  rcases houtRightHave with ⟨consumed2, padding2, hcfgRight⟩
  subst cfgRight

  obtain ⟨m4, hm4, h4⟩ :=
    andRightReturn_loop_reaches_have
      witness tail (encodeEvalFrames frames)
      consumed2 padding2
      (evalCircuit sigma left) (evalCircuit sigma right)

  let finalValue :=
    Bool.and (evalCircuit sigma left) (evalCircuit sigma right)
  let cHave : LoopConfig :=
    { state := .have (.start finalValue),
      tape :=
        evalCursorStackEndTape witness consumed2 tail
          (encodeEvalFrames frames) (padding2 + 3) }

  have h4' :
      cHave ∈
        evalRunLoopMachine.runBranches m4
          [{ state := .have (.start (evalCircuit sigma right)),
             tape :=
               evalCursorStackEndTape witness consumed2 tail
                 (encodeEvalFrames
                   (.andRight (evalCircuit sigma left) :: frames))
                 padding2 }] := by
    simpa [cHave, finalValue, encodeEvalFrames, List.append_assoc] using h4

  have h01234 :=
    mem_runBranches_trans evalRunLoopMachine
      (m0 + m1 + m2 + m3) m4
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.and left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have (.start (evalCircuit sigma right)),
         tape :=
           evalCursorStackEndTape witness consumed2 tail
             (encodeEvalFrames
               (.andRight (evalCircuit sigma left) :: frames))
             padding2 } : LoopConfig)
      cHave h0123 h4'

  obtain ⟨m5, cfgFinal, h5, hout5⟩ :=
    have_reaches_outcome
      witness finalValue tail frames consumed2 (padding2 + 3)

  have hAll :=
    mem_runBranches_trans evalRunLoopMachine
      (m0 + m1 + m2 + m3 + m4) m5
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.and left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cHave cfgFinal h01234 h5

  refine ⟨m0 + m1 + m2 + m3 + m4 + m5, cfgFinal, hAll, ?_⟩
  simpa [finalValue, evalCircuit] using hout5

#print axioms MCore.Real.P01EvalRunCircuitCertificate.encodeCircuit_ne_nil
#print axioms MCore.Real.P01EvalRunCircuitCertificate.and_certificate

/-- Structural producer for disjunction. The physical loop evaluates the left
child under an orLeft frame, converts that frame to orRight carrying the
left value, evaluates the right child, combines both Booleans, and normalizes
the resulting haveValue state into the external circuit outcome. -/
theorem or_certificate
    (sigma : Assignment)
    (witness : BitString)
    (left right : Circuit)
    (hleft : CircuitRunCertificate sigma witness left)
    (hright : CircuitRunCertificate sigma witness right) :
    CircuitRunCertificate sigma witness (.or left right) := by
  intro tail frames consumed padding hlen hread

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

  obtain ⟨m0, hm0, h0⟩ :=
    or_loop_reaches_need
      witness
      (encodeCircuit left ++ encodeCircuit right ++ tail)
      (encodeEvalFrames frames) consumed padding

  let padLeft := ((padding - 1) - 1) - 1
  let cNeedLeft : LoopConfig :=
    { state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrame .orLeft ++ encodeEvalFrames frames)
          padLeft }

  have h0' :
      cNeedLeft ∈
        evalRunLoopMachine.runBranches m0
          [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.or left right) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cNeedLeft, padLeft, encodeCircuit, List.append_assoc] using h0

  obtain ⟨m1, cfgLeft, h1, hout1⟩ :=
    hleft (encodeCircuit right ++ tail) (.orLeft :: frames)
      (consumed + 3) padLeft hlenLeft hreadLeft

  have h1' :
      cfgLeft ∈ evalRunLoopMachine.runBranches m1 [cNeedLeft] := by
    simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1

  have h01 :=
    mem_runBranches_trans evalRunLoopMachine
      m0 m1
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeedLeft cfgLeft h0' h1'

  have hRightTail :
      encodeCircuit right ++ tail ≠ [] := by
    intro hnil
    have henc : encodeCircuit right = [] := by
      exact (List.append_eq_nil.mp hnil).1
    exact encodeCircuit_ne_nil right henc

  have houtLeftHave :
      ∃ consumed1 padding1,
        cfgLeft =
          { state := .have (.start (evalCircuit sigma left)),
            tape :=
              evalCursorStackEndTape witness consumed1
                (encodeCircuit right ++ tail)
                (encodeEvalFrames (.orLeft :: frames))
                padding1 } := by
    cases htail : encodeCircuit right ++ tail with
    | nil =>
        exact False.elim (hRightTail htail)
    | cons b bs =>
        have htmp :
            ∃ consumed1 padding1,
              cfgLeft =
                { state := .have (.start (evalCircuit sigma left)),
                  tape :=
                    evalCursorStackEndTape witness consumed1
                      (b :: bs)
                      (encodeEvalFrames (.orLeft :: frames))
                      padding1 } := by
          simpa [LoopOutcome, htail] using hout1
        rcases htmp with ⟨consumed1, padding1, hcfg⟩
        refine ⟨consumed1, padding1, ?_⟩
        simpa [htail] using hcfg

  rcases houtLeftHave with ⟨consumed1, padding1, hcfgLeft⟩
  subst cfgLeft

  obtain ⟨m2, hm2, h2⟩ :=
    orLeftReturn_loop_reaches_need
      witness (encodeCircuit right ++ tail)
      (encodeEvalFrames frames)
      consumed1 padding1 (evalCircuit sigma left)

  let padRight := (((padding1 + 3) - 1) - 1) - 1
  let cNeedRight : LoopConfig :=
    { state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness consumed1
          (encodeCircuit right ++ tail)
          (encodeEvalFrame (.orRight (evalCircuit sigma left)) ++
            encodeEvalFrames frames)
          padRight }

  have h2' :
      cNeedRight ∈
        evalRunLoopMachine.runBranches m2
          [{ state := .have (.start (evalCircuit sigma left)),
             tape :=
               evalCursorStackEndTape witness consumed1
                 (encodeCircuit right ++ tail)
                 (encodeEvalFrames (.orLeft :: frames))
                 padding1 }] := by
    simpa [cNeedRight, padRight, encodeEvalFrames, List.append_assoc] using h2

  have h012 :=
    mem_runBranches_trans evalRunLoopMachine
      (m0 + m1) m2
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have (.start (evalCircuit sigma left)),
         tape :=
           evalCursorStackEndTape witness consumed1
             (encodeCircuit right ++ tail)
             (encodeEvalFrames (.orLeft :: frames))
             padding1 } : LoopConfig)
      cNeedRight h01 h2'

  obtain ⟨m3, cfgRight, h3, hout3⟩ :=
    hright tail (.orRight (evalCircuit sigma left) :: frames)
      consumed1 padRight hlenRight hreadRight

  have h3' :
      cfgRight ∈
        evalRunLoopMachine.runBranches m3 [cNeedRight] := by
    simpa [cNeedRight, encodeEvalFrames, List.append_assoc] using h3

  have h0123 :=
    mem_runBranches_trans evalRunLoopMachine
      (m0 + m1 + m2) m3
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeedRight cfgRight h012 h3'

  have houtRightHave :
      ∃ consumed2 padding2,
        cfgRight =
          { state := .have (.start (evalCircuit sigma right)),
            tape :=
              evalCursorStackEndTape witness consumed2 tail
                (encodeEvalFrames
                  (.orRight (evalCircuit sigma left) :: frames))
                padding2 } := by
    simpa [LoopOutcome] using hout3

  rcases houtRightHave with ⟨consumed2, padding2, hcfgRight⟩
  subst cfgRight

  obtain ⟨m4, hm4, h4⟩ :=
    orRightReturn_loop_reaches_have
      witness tail (encodeEvalFrames frames)
      consumed2 padding2
      (evalCircuit sigma left) (evalCircuit sigma right)

  let finalValue :=
    Bool.or (evalCircuit sigma left) (evalCircuit sigma right)
  let cHave : LoopConfig :=
    { state := .have (.start finalValue),
      tape :=
        evalCursorStackEndTape witness consumed2 tail
          (encodeEvalFrames frames) (padding2 + 3) }

  have h4' :
      cHave ∈
        evalRunLoopMachine.runBranches m4
          [{ state := .have (.start (evalCircuit sigma right)),
             tape :=
               evalCursorStackEndTape witness consumed2 tail
                 (encodeEvalFrames
                   (.orRight (evalCircuit sigma left) :: frames))
                 padding2 }] := by
    simpa [cHave, finalValue, encodeEvalFrames, List.append_assoc] using h4

  have h01234 :=
    mem_runBranches_trans evalRunLoopMachine
      (m0 + m1 + m2 + m3) m4
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have (.start (evalCircuit sigma right)),
         tape :=
           evalCursorStackEndTape witness consumed2 tail
             (encodeEvalFrames
               (.orRight (evalCircuit sigma left) :: frames))
             padding2 } : LoopConfig)
      cHave h0123 h4'

  obtain ⟨m5, cfgFinal, h5, hout5⟩ :=
    have_reaches_outcome
      witness finalValue tail frames consumed2 (padding2 + 3)

  have hAll :=
    mem_runBranches_trans evalRunLoopMachine
      (m0 + m1 + m2 + m3 + m4) m5
      [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cHave cfgFinal h01234 h5

  refine ⟨m0 + m1 + m2 + m3 + m4 + m5, cfgFinal, hAll, ?_⟩
  simpa [finalValue, evalCircuit] using hout5

#print axioms MCore.Real.P01EvalRunCircuitCertificate.encodeCircuit_ne_nil
#print axioms MCore.Real.P01EvalRunCircuitCertificate.and_certificate




/-- Full structural semantic/run certificate for every circuit. -/
theorem circuit_certificate
    (sigma : Assignment)
    (witness : BitString) :
    ∀ circuit : Circuit,
      CircuitRunCertificate sigma witness circuit := by
  intro circuit
  induction circuit with
  | input i =>
      exact input_certificate sigma witness i
  | const b =>
      exact const_certificate sigma witness b
  | not c ih =>
      exact neg_certificate sigma witness c ih
  | and a b iha ihb =>
      exact and_certificate sigma witness a b iha ihb
  | or a b iha ihb =>
      exact or_certificate sigma witness a b iha ihb

#print axioms MCore.Real.P01EvalRunCircuitCertificate.circuit_certificate

#print axioms MCore.Real.P01EvalRunCircuitCertificate.input_certificate
#print axioms MCore.Real.P01EvalRunCircuitCertificate.constFalse_certificate
#print axioms MCore.Real.P01EvalRunCircuitCertificate.constTrue_certificate
#print axioms MCore.Real.P01EvalRunCircuitCertificate.const_certificate
#print axioms MCore.Real.P01EvalRunCircuitCertificate.neg_certificate

end P01EvalRunCircuitCertificate
end Real
end MCore
