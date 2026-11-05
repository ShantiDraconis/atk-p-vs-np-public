import MCore.Real.P01WitnessIndexedRead
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PreservingUnaryReadMachine

open CanonicalFinalProof
open P01WitnessIndexedRead

/-- Finite control for a reversible/preserving unary indexed witness reader.
The only data carried in control are at most the currently moved witness bit
and the final result bit.  The unbounded index remains tape data. -/
inductive PreserveReadState where
  | start
  | seekWitness
  | carryToTerm (moved : Bool)
  | bufferEnter (moved : Bool)
  | bufferScan (moved : Bool)
  | returnDelimiter
  | returnUnary
  | seekTarget
  | toTermAfterRead (result : Bool)
  | restoreDelimiter (result : Bool)
  | bufferCheck (result : Bool)
  | bufferScanEnd (result : Bool)
  | bufferPop (result : Bool)
  | restoreBufferLeft (result moved : Bool)
  | restoreAcrossTerm (result moved : Bool)
  | restoreSeekSlot (result moved : Bool)
  | restoreWrite (result moved : Bool)
  | finishDelimiter (result : Bool)
  | finishTerm (result : Bool)
  | haltFalse
  | haltTrue
  | reject
  deriving DecidableEq, Repr

/-- Fixed one-tape preserving reader.

Forward phase:
* erase one unary true marker;
* remove the next witness-prefix bit;
* append that bit to a buffer to the right of a blank delimiter after the
  unary false terminator;
* return to the first remaining unary marker.

Restoration phase:
* read the target witness bit without erasing it;
* pop the right buffer from its end;
* restore each skipped witness bit into the nearest blank slot;
* when the buffer is empty, erase the unary false terminator and halt with the
  target Boolean encoded only in the terminal control state. -/
def preservingUnaryReadMachine : TM PreserveReadState (Option Bool) :=
  { initial := .start
    blank := none
    transition := fun q symbol =>
      match q with
      | .start =>
          match symbol with
          | some true => (.seekWitness, none, .left)
          | some false => (.seekTarget, some false, .left)
          | none => (.reject, none, .stay)
      | .seekWitness =>
          match symbol with
          | none => (.seekWitness, none, .left)
          | some b => (.carryToTerm b, none, .right)
      | .carryToTerm b =>
          match symbol with
          | none => (.carryToTerm b, none, .right)
          | some true => (.carryToTerm b, some true, .right)
          | some false => (.bufferEnter b, some false, .right)
      | .bufferEnter b =>
          match symbol with
          | none => (.bufferScan b, none, .right)
          | some x => (.reject, some x, .stay)
      | .bufferScan b =>
          match symbol with
          | some x => (.bufferScan b, some x, .right)
          | none => (.returnDelimiter, some b, .left)
      | .returnDelimiter =>
          match symbol with
          | none => (.returnUnary, none, .left)
          | some x => (.reject, some x, .stay)
      | .returnUnary =>
          match symbol with
          | some x => (.returnUnary, some x, .left)
          | none => (.start, none, .right)
      | .seekTarget =>
          match symbol with
          | none => (.seekTarget, none, .left)
          | some b => (.toTermAfterRead b, some b, .right)
      | .toTermAfterRead r =>
          match symbol with
          | none => (.toTermAfterRead r, none, .right)
          | some false => (.restoreDelimiter r, some false, .right)
          | some true => (.reject, some true, .stay)
      | .restoreDelimiter r =>
          match symbol with
          | none => (.bufferCheck r, none, .right)
          | some x => (.reject, some x, .stay)
      | .bufferCheck r =>
          match symbol with
          | none => (.finishDelimiter r, none, .left)
          | some x => (.bufferScanEnd r, some x, .right)
      | .bufferScanEnd r =>
          match symbol with
          | some x => (.bufferScanEnd r, some x, .right)
          | none => (.bufferPop r, none, .left)
      | .bufferPop r =>
          match symbol with
          | some b => (.restoreBufferLeft r b, none, .left)
          | none => (.reject, none, .stay)
      | .restoreBufferLeft r b =>
          match symbol with
          | some x => (.restoreBufferLeft r b, some x, .left)
          | none => (.restoreAcrossTerm r b, none, .left)
      | .restoreAcrossTerm r b =>
          match symbol with
          | some false => (.restoreSeekSlot r b, some false, .left)
          | some true => (.reject, some true, .stay)
          | none => (.reject, none, .stay)
      | .restoreSeekSlot r b =>
          match symbol with
          | none => (.restoreSeekSlot r b, none, .left)
          | some x => (.restoreWrite r b, some x, .right)
      | .restoreWrite r b =>
          match symbol with
          | none => (.toTermAfterRead r, some b, .right)
          | some x => (.reject, some x, .stay)
      | .finishDelimiter r =>
          match symbol with
          | none => (.finishTerm r, none, .left)
          | some x => (.reject, some x, .stay)
      | .finishTerm r =>
          match symbol with
          | some false =>
              if r then (.haltTrue, none, .stay)
              else (.haltFalse, none, .stay)
          | some true => (.reject, some true, .stay)
          | none => (.reject, none, .stay)
      | .haltFalse => (.haltFalse, symbol, .stay)
      | .haltTrue => (.haltTrue, symbol, .stay)
      | .reject => (.reject, symbol, .stay)
    halting := fun q =>
      match q with
      | .haltFalse => true
      | .haltTrue => true
      | .reject => true
      | _ => false }

/-- Terminal Boolean produced by the preserving machine. -/
def preservingUnaryReadValue : PreserveReadState → Option Bool
  | .haltFalse => some false
  | .haltTrue => some true
  | _ => none

@[simp] theorem preservingUnaryReadMachine_blank :
    preservingUnaryReadMachine.blank = none := rfl

@[simp] theorem preservingUnaryReadMachine_initial :
    preservingUnaryReadMachine.initial = PreserveReadState.start := rfl

/-- Conservative cubic envelope for repeated witness/source/buffer shuttles. -/
def preservingUnaryReadTimeBound : TimeBound :=
  fun n => 128 * (n + 1) ^ 3

theorem preservingUnaryReadTimeBound_poly :
    PolynomialTimeBound preservingUnaryReadTimeBound := by
  exact ⟨128, 3, fun n => Nat.le_refl _⟩

/-- The zero index immediately enters target-seek mode without deleting a
witness cell. -/
theorem zero_index_dispatch
    (witness : BitString) :
    preservingUnaryReadMachine.step
      { state := .start, tape := witnessReadTape witness 0 } =
      { state := .seekTarget,
        tape :=
          Tape.move none .left
            ((witnessReadTape witness 0).write (some false)) } := by
  simp [preservingUnaryReadMachine, witnessReadTape, encodeNat, TM.step,
    Tape.write]

/-- Every positive unary index begins by consuming exactly one true marker and
moves left toward the next witness-prefix cell. -/
theorem succ_index_dispatch
    (witness : BitString) (i : Nat) :
    preservingUnaryReadMachine.step
      { state := .start, tape := witnessReadTape witness (i + 1) } =
      { state := .seekWitness,
        tape :=
          Tape.move none .left
            ((witnessReadTape witness (i + 1)).write none) } := by
  simp [preservingUnaryReadMachine, witnessReadTape, encodeNat, TM.step,
    Tape.write]

@[simp] theorem haltFalse_value :
    preservingUnaryReadValue .haltFalse = some false := rfl

@[simp] theorem haltTrue_value :
    preservingUnaryReadValue .haltTrue = some true := rfl

#print axioms MCore.Real.P01PreservingUnaryReadMachine.preservingUnaryReadTimeBound_poly
#print axioms MCore.Real.P01PreservingUnaryReadMachine.zero_index_dispatch
#print axioms MCore.Real.P01PreservingUnaryReadMachine.succ_index_dispatch

end P01PreservingUnaryReadMachine
end Real
end MCore
