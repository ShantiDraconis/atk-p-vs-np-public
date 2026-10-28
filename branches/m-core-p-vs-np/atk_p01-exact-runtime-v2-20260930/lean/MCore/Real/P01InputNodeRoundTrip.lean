import MCore.Real.P01EvalInputNodePhysicalRefinement
import MCore.Real.P01InputIndexLookahead
import MCore.Real.P01InputAfterReadReturn

namespace MCore
namespace Real
namespace P01InputNodeRoundTrip

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EvalCursorMachine
open P01EvalInputNodePhysicalRefinement
open P01WitnessIndexedReadPreserving
open P01WitnessIndexedReadGap
open P01WitnessIndexedReadGapRaw
open P01InputReturnMode
open P01InputIndexLookahead
open P01InputAfterReadReturn

/-- Number of source cells erased after consuming the unary index. -/
def consumedAfterInputIndex (consumed i : Nat) : Nat :=
  consumed + i + 1

/-- Exact return fuel selected from the finite return mode encoded by
`tail`/ `frameStack`. -/
def inputAfterReadReturnFuel
    (consumed : Nat) (tail frameStack : BitString) : Nat :=
  match tail with
  | _ :: _ => consumed + tail.length + frameStack.length + 3
  | [] =>
      match frameStack with
      | _ :: _ => consumed + frameStack.length + 3
      | [] => 1


/-- Uniform linear envelope for the mode-aware return phase. -/
theorem inputAfterReadReturnFuel_le
    (consumed : Nat) (tail frameStack : BitString) :
    inputAfterReadReturnFuel consumed tail frameStack ≤
      consumed + tail.length + frameStack.length + 3 := by
  cases tail with
  | cons b bs =>
      simp [inputAfterReadReturnFuel]
  | nil =>
      cases frameStack with
      | cons f fs =>
          simp [inputAfterReadReturnFuel]
      | nil =>
          simp [inputAfterReadReturnFuel]

/-- Canonical terminal configuration of the mode-aware return phase.

When no source and no frames remain, the evaluator already has its final value,
so no stack-end normalization is required. -/
def inputAfterReadTarget
    (witness : BitString)
    (consumed : Nat)
    (tail frameStack : BitString)
    (padding : Nat) :
    Configuration InputAfterReadReturnState (Option Bool) :=
  match tail with
  | _ :: _ =>
      { state := .halt .frameStack,
        tape := evalCursorStackEndTape witness consumed tail frameStack padding }
  | [] =>
      match frameStack with
      | _ :: _ =>
          { state := .halt .frameStack,
            tape := evalCursorStackEndTape witness consumed [] frameStack padding }
      | [] =>
          { state := .halt .done,
            tape := afterIndexedReadTape witness consumed [] [] padding }

/-- The full-layout preserving reader lands exactly on the canonical
`afterIndexedReadTape` expected by the mode-aware return machine. -/
theorem inputNode000_read_to_afterIndexedReadTape
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    preservingReadMachine.run (preservingReadGapFuel consumed i)
      { state := preservingReadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ tail) frameStack padding } =
      { state := .halt (witness.getD i false),
        tape :=
          afterIndexedReadTape witness
            (consumedAfterInputIndex consumed i)
            tail frameStack padding } := by
  simpa [afterIndexedReadTape, consumedAfterInputIndex,
    inputNodeRawSuffix, List.append_assoc] using
    inputNode000_full_layout_read
      witness tail frameStack consumed padding i hi

/-- Uniform return theorem after an indexed input read. -/
theorem inputNode000_afterRead_return
    (witness tail frameStack : BitString)
    (consumed padding : Nat) :
    inputAfterReadReturnMachine.run
      (inputAfterReadReturnFuel consumed tail frameStack)
      { state := .start (inputReturnModeOf tail frameStack),
        tape := afterIndexedReadTape witness consumed
          tail frameStack padding } =
      inputAfterReadTarget witness consumed tail frameStack padding := by
  cases tail with
  | cons b bs =>
      simpa [inputAfterReadReturnFuel, inputAfterReadTarget,
        inputReturnModeOf] using
        return_sourceTail witness consumed b bs frameStack padding
  | nil =>
      cases frameStack with
      | cons b bs =>
          simpa [inputAfterReadReturnFuel, inputAfterReadTarget,
            inputReturnModeOf] using
            return_frameStack witness consumed b bs padding
      | nil =>
          simpa [inputAfterReadReturnFuel, inputAfterReadTarget,
            inputReturnModeOf] using
            return_done witness consumed padding

/-- Three certified physical phases for the input tag:
1. finite lookahead computes the return mode without changing the tape;
2. the preserving reader consumes the unary index and restores the witness;
3. the mode-aware return restores the evaluator cursor (or stops locally in
   final-value mode).

This theorem is intentionally a phase certificate, not yet a claim that the
three transition tables have been fused into one `TM (Fin n)`. -/
theorem inputNode000_phase_pipeline
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    inputIndexLookaheadMachine.run (2 * i + 6)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ tail) frameStack padding } =
      { state := .halt (inputReturnModeOf tail frameStack),
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ tail) frameStack padding } ∧
    preservingReadMachine.run (preservingReadGapFuel consumed i)
      { state := preservingReadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ tail) frameStack padding } =
      { state := .halt (witness.getD i false),
        tape :=
          afterIndexedReadTape witness
            (consumedAfterInputIndex consumed i)
            tail frameStack padding } ∧
    inputAfterReadReturnMachine.run
      (inputAfterReadReturnFuel
        (consumedAfterInputIndex consumed i) tail frameStack)
      { state := .start (inputReturnModeOf tail frameStack),
        tape :=
          afterIndexedReadTape witness
            (consumedAfterInputIndex consumed i)
            tail frameStack padding } =
      inputAfterReadTarget witness
        (consumedAfterInputIndex consumed i)
        tail frameStack padding := by
  constructor
  · exact lookahead_inputReturnMode
      witness tail frameStack consumed padding i
  constructor
  · exact inputNode000_read_to_afterIndexedReadTape
      witness tail frameStack consumed padding i hi
  · exact inputNode000_afterRead_return
      witness tail frameStack
      (consumedAfterInputIndex consumed i) padding

#print axioms MCore.Real.P01InputNodeRoundTrip.inputAfterReadReturnFuel_le
#print axioms MCore.Real.P01InputNodeRoundTrip.inputNode000_read_to_afterIndexedReadTape
#print axioms MCore.Real.P01InputNodeRoundTrip.inputNode000_afterRead_return
#print axioms MCore.Real.P01InputNodeRoundTrip.inputNode000_phase_pipeline

end P01InputNodeRoundTrip
end Real
end MCore
