import MCore.Real.P01WitnessIndexedReadPreserving
import MCore.Real.P01WitnessIndexedReadGapRaw
import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01FullVerifierInputShuttleV2
import MCore.Real.P01EvalTagPhysicalRefinement
import MCore.Real.P01EncodedFrameTape
import MCore.Real.P01EncodedStackEvaluator

namespace MCore
namespace Real
namespace P01EvalInputNodePhysicalRefinement

open CanonicalFinalProof
open CanonicalCircuitBits
open CircuitK1
open P01WitnessIndexedReadPreserving
open P01WitnessIndexedReadGap
open P01WitnessIndexedReadGapRaw
open P01EvalCursorMachine
open P01FullVerifierPhysicalStackV2
open P01FullVerifierPhysicalMoves
open P01FullVerifierInputShuttleV2
open P01EncodedStackEvaluator
open P01EncodedFrameTape

/-- The source bits of an encoded input node.  The witness is not appended to
this bitstring; it lives in the separate witness region of the physical tape. -/
def inputNode000Bits (i : Nat) : BitString :=
  [false, false, false] ++ encodeNat i

@[simp] theorem inputNode000Bits_eq_encodeCircuit (i : Nat) :
    inputNode000Bits i = encodeCircuit (.input i) := by
  rfl

/-- Canonical assignment induced directly by a physical witness bitstring. -/
def assignmentOfBits (witness : BitString) : Assignment :=
  fun i => witness.getD i false

/-- The logical streaming evaluator consumes exactly the input-node encoding
and returns the selected witness value. -/
theorem evalStep_inputNode000
    (witness tail : BitString)
    (i : Nat)
    (frames : List EvalFrame) :
    evalStep (assignmentOfBits witness)
        (needExpr (inputNode000Bits i ++ tail) frames) =
      some
        (haveValue (witness.getD i false) tail frames) := by
  simp [inputNode000Bits, assignmentOfBits, evalStep, needExpr, haveValue,
    decodeNat_encodeNat_append]

/-- On a valid witness index, list default lookup agrees with bounded lookup. -/
theorem getD_eq_getElem_of_lt
    (witness : BitString) (i : Nat)
    (hi : i < witness.length) :
    witness.getD i false = witness[i] := by
  induction witness generalizing i with
  | nil =>
      simp at hi
  | cons b bs ih =>
      cases i with
      | zero =>
          rfl
      | succ i =>
          have hi' : i < bs.length := by
            simpa using hi
          simpa using ih i hi'

/-- The already-certified V2 physical shuttle reads exactly the same Boolean
selected by the logical input-node semantics. -/
theorem moveToWitnessSeqV2_head_refines_inputNode000
    (witness tail : BitString)
    (i : Nat)
    (frames : List EvalFrame)
    (padding : Nat)
    (hi : i < witness.length) :
    (execMoves none
      (moveToWitnessSeqV2
        (encodeEvalFrames frames)
        (inputNode000Bits i ++ tail)
        i)
      (physicalStackV2Tape
        witness
        (inputNode000Bits i ++ tail)
        (encodeEvalFrames frames)
        padding)).head =
      some (witness.getD i false) := by
  rw [moveToWitnessSeqV2_head_correct
    witness
    (inputNode000Bits i ++ tail)
    (encodeEvalFrames frames)
    padding i hi]
  rw [getD_eq_getElem_of_lt witness i hi]

/-- The preserving unary-index reader returns the same selected Boolean on its
canonical local input layout. -/
theorem preservingRead_refines_inputNode000_value
    (witness tail : BitString)
    (i : Nat)
    (hi : i < witness.length) :
    (preservingReadMachine.run (preservingReadFuel i)
      { state := preservingReadMachine.initial,
        tape := preservingReadTape witness i tail }).state =
      .halt (assignmentOfBits witness i) := by
  simpa [assignmentOfBits] using
    preservingRead_forall_value i witness tail hi

/-- Value-level input-node refinement: logical semantics, the V2 witness
shuttle, and the preserving unary-index reader all select the same witness bit.

This intentionally does not claim the still-open full-layout TM composition.
That next step must adapt the streaming cursor layout to the preserving reader
inside one fixed finite-control verifier. -/
theorem inputNode000_value_refinement
    (witness tail : BitString)
    (i : Nat)
    (frames : List EvalFrame)
    (padding : Nat)
    (hi : i < witness.length) :
    evalStep (assignmentOfBits witness)
        (needExpr (inputNode000Bits i ++ tail) frames) =
        some (haveValue (witness.getD i false) tail frames) ∧
    (execMoves none
      (moveToWitnessSeqV2
        (encodeEvalFrames frames)
        (inputNode000Bits i ++ tail)
        i)
      (physicalStackV2Tape
        witness
        (inputNode000Bits i ++ tail)
        (encodeEvalFrames frames)
        padding)).head =
        some (witness.getD i false) ∧
    (preservingReadMachine.run (preservingReadFuel i)
      { state := preservingReadMachine.initial,
        tape := preservingReadTape witness i tail }).state =
        .halt (witness.getD i false) := by
  constructor
  · exact evalStep_inputNode000 witness tail i frames
  constructor
  · exact moveToWitnessSeqV2_head_refines_inputNode000
      witness tail i frames padding hi
  · exact preservingRead_forall_value i witness tail hi


/-- Exact raw physical suffix following an input-node unary index in the
streaming cursor layout. -/
def inputNodeRawSuffix
    (tail frameStack : BitString) (padding : Nat) :
    List (Option Bool) :=
  tail.map some ++
    none :: frameStack.reverse.map some ++
    none :: List.replicate padding none

/-- The actual streaming cursor tape at the beginning of the unary index is
definitionally the gap-aware preserving-reader layout, with \`consumed\` as the
physical blank gap. -/
theorem evalCursorReadTape_eq_preservingReadGapRawTape
    (witness tail frameStack : BitString)
    (consumed padding i : Nat) :
    evalCursorReadTape witness consumed
        (encodeNat i ++ tail) frameStack padding =
      preservingReadGapRawTape witness consumed i
        (inputNodeRawSuffix tail frameStack padding) := by
  cases i with
  | zero =>
      simp [evalCursorReadTape, preservingReadGapRawTape,
        gapReadRawTape, inputNodeRawSuffix, encodeNat,
        List.map_append, List.append_assoc]
  | succ i =>
      simp [evalCursorReadTape, preservingReadGapRawTape,
        gapReadRawTape, inputNodeRawSuffix, encodeNat,
        List.map_append, List.append_assoc]

/-- Full-layout preserving read for the input-node index.  This is the exact
physical cursor layout used by the evaluator: witness, arbitrary consumed
blank gap, unary index, unread source tail, frame separator, reversed frames,
stack-end separator, and padding are all preserved. -/
theorem inputNode000_full_layout_read
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
          { left := witness.map some,
            head := none,
            right :=
              List.replicate (consumed + i + 1) none ++
                inputNodeRawSuffix tail frameStack padding } } := by
  rw [evalCursorReadTape_eq_preservingReadGapRawTape]
  exact preservingReadGapRaw_forall
    i witness (inputNodeRawSuffix tail frameStack padding) consumed hi

theorem inputNode000_full_layout_value
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    (preservingReadMachine.run (preservingReadGapFuel consumed i)
      { state := preservingReadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ tail) frameStack padding }).state =
      .halt (witness.getD i false) := by
  rw [inputNode000_full_layout_read witness tail frameStack
    consumed padding i hi]

#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.evalCursorReadTape_eq_preservingReadGapRawTape
#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.inputNode000_full_layout_read
#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.inputNode000_full_layout_value


#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.evalStep_inputNode000
#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.getD_eq_getElem_of_lt
#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.moveToWitnessSeqV2_head_refines_inputNode000
#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.preservingRead_refines_inputNode000_value
#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.inputNode000_value_refinement

end P01EvalInputNodePhysicalRefinement
end Real
end MCore
