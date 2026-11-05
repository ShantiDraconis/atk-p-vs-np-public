import MCore.Real.P01WitnessIndexedReadPreserving
import MCore.Real.P01FullVerifierInputShuttleV2
import MCore.Real.P01EvalTagPhysicalRefinement
import MCore.Real.P01EncodedFrameTape
import MCore.Real.P01EncodedStackEvaluator
import MCore.Real.P01EvalCursorConsume
import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01GapPreservingRead

namespace MCore
namespace Real
namespace P01EvalInputNodePhysicalRefinement

open CanonicalFinalProof
open CanonicalCircuitBits
open CircuitK1
open P01WitnessIndexedReadPreserving
open P01FullVerifierPhysicalStackV2
open P01FullVerifierPhysicalMoves
open P01FullVerifierInputShuttleV2
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorConsume
open P01EvalCursorMachine
open P01GapPreservingRead

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


/-- Physical suffix to the right of the unread source while the cursor is at
the first unread source bit. -/
def inputReadSuffix
    (frames : List EvalFrame) (padding : Nat) :
    List (Option Bool) :=
  none :: (encodeEvalFrames frames).reverse.map some ++
    none :: List.replicate padding none

/-- After consuming the three-bit input tag and seeking the next unread source
bit, the physical tape is exactly the canonical gapped preserving-reader
configuration.  This is the representation bridge that was missing from the
older value-only refinement. -/
theorem input_cursor_is_gapReadConfig
    (witness : BitString)
    (consumed i : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    let frameBits := encodeEvalFrames frames
    let tagged := false :: false :: false :: (encodeNat i ++ rest)
    let afterTag :=
      consumeThreeTape witness consumed tagged frameBits padding
    let seekFinal :=
      cursorSeekMachine.run
        (frameBits.length + (encodeNat i ++ rest).length + 3)
        { state := CursorSeekState.start, tape := afterTag }
    seekFinal.tape =
      (gapReadConfig witness (consumed + 3) i rest
        (inputReadSuffix frames padding)).tape := by
  dsimp
  rw [consumeThreeTape_correct]
  rw [cursorSeek_run]
  cases i <;>
    simp [evalCursorReadTape, gapReadConfig, gapReadTape,
      inputReadSuffix, encodeNat, List.append_assoc]

/-- Full local physical input-node refinement on the streaming cursor layout.
It connects the frozen semantic evaluator directly to the closed gap-tolerant
preserving reader and proves the exact resulting tape. -/
theorem evalStep_inputNode000_full_layout
    (witness : BitString)
    (consumed i : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat)
    (hi : i < witness.length) :
    let sigma := assignmentOfBits witness
    let frameBits := encodeEvalFrames frames
    let tagged := false :: false :: false :: (encodeNat i ++ rest)
    let afterTag :=
      consumeThreeTape witness consumed tagged frameBits padding
    let seekFinal :=
      cursorSeekMachine.run
        (frameBits.length + (encodeNat i ++ rest).length + 3)
        { state := CursorSeekState.start, tape := afterTag }
    let readFinal :=
      gapReadMachine.run (gapReadFuel (consumed + 3) i)
        { state := gapReadMachine.initial, tape := seekFinal.tape }
    evalStep sigma (needExpr tagged frames) =
        some (haveValue (witness.getD i false) rest frames) ∧
      readFinal.state = .halt (witness.getD i false) ∧
      readFinal.tape =
        { left := witness.map some,
          head := none,
          right :=
            List.replicate (consumed + 3 + i + 1) none ++
              (rest.map some ++ inputReadSuffix frames padding) } := by
  dsimp
  constructor
  · simpa [inputNode000Bits, assignmentOfBits] using
      evalStep_inputNode000 witness rest i frames
  · have hbridge :=
      input_cursor_is_gapReadConfig witness consumed i rest frames padding
    rw [hbridge]
    have hrun :=
      gapRead_forall witness rest (consumed + 3) i
        (inputReadSuffix frames padding) hi
    have hcfg :
        ({ state := gapReadMachine.initial,
           tape :=
             (gapReadConfig witness (consumed + 3) i rest
               (inputReadSuffix frames padding)).tape } :
          Configuration PreservingReadState (Option Bool)) =
        gapReadConfig witness (consumed + 3) i rest
          (inputReadSuffix frames padding) := by
      cases i <;> rfl
    rw [hcfg, hrun]
    exact ⟨rfl, rfl⟩

#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.input_cursor_is_gapReadConfig
#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.evalStep_inputNode000_full_layout

#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.evalStep_inputNode000
#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.getD_eq_getElem_of_lt
#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.moveToWitnessSeqV2_head_refines_inputNode000
#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.preservingRead_refines_inputNode000_value
#print axioms MCore.Real.P01EvalInputNodePhysicalRefinement.inputNode000_value_refinement

end P01EvalInputNodePhysicalRefinement
end Real
end MCore
