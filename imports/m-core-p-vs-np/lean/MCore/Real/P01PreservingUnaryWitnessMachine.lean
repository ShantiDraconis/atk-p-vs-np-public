import MCore.Real.P01InputNodePreservingPlan
import MCore.Real.P01WitnessIndexedRead

namespace MCore
namespace Real
namespace P01PreservingUnaryWitnessMachine

open CanonicalFinalProof
open P01WitnessIndexedRead
open CanonicalCircuitBits

/-!
# Fixed-control preserving unary-index reader

This is the concrete driver skeleton for the remaining P01 input-node case.
It uses no Nat-valued control state.

Protocol on witnessReadTape witness i:
* index0 handles the zero-index terminator directly;
* the first unary true moves the separator marker one witness cell left;
* indexSome repeats: erased unary cells are scanned as blanks, traversed
  witness cells are scanned as Booleans, and the unique marker blank is moved
  one witness cell deeper;
* at the false terminator the selected witness bit is remembered in one of two
  finite states;
* the marker is moved back across the traversed pref, restoring every witness
  cell exactly;
* erased unary cells and the false terminator are consumed; the result is
  encoded only by haltFalse / haltTrue.

The global successor-index induction is proved separately; this file fixes the
actual finite transition graph and proves the complete zero-index execution.
-/

inductive PreservingReadState where
  | index0
  | indexSome
  | firstMarker
  | seekBlanks
  | seekBits
  | shiftRead
  | carryFalse
  | carryTrue
  | returnFromMarker
  | returnBits
  | returnBlanks
  | finalZeroSep
  | finalZeroRead
  | finalZeroBackFalse
  | finalZeroBackTrue
  | finalZeroTermFalse
  | finalZeroTermTrue
  | finalSeekBlanks
  | finalSeekBits
  | finalRead
  | selectedFalse
  | selectedTrue
  | rewindInspectFalse
  | rewindInspectTrue
  | rewindCarryFF
  | rewindCarryFT
  | rewindCarryTF
  | rewindCarryTT
  | rewindAtMarkerFalse
  | rewindAtMarkerTrue
  | cleanupFalse
  | cleanupTrue
  | haltFalse
  | haltTrue
  | reject
  deriving DecidableEq, Repr

def preservingUnaryReadMachine : TM PreservingReadState (Option Bool) :=
  { initial := .index0
    blank := none
    transition := fun q symbol =>
      match q with
      | .index0 =>
          match symbol with
          | some true => (.firstMarker, none, .left)
          | some false => (.finalZeroSep, some false, .left)
          | none => (.reject, none, .stay)
      | .indexSome =>
          match symbol with
          | some true => (.seekBlanks, none, .left)
          | some false => (.finalSeekBlanks, some false, .left)
          | none => (.reject, none, .stay)

      -- first true: the head is now directly on the original separator marker
      | .firstMarker =>
          match symbol with
          | none => (.shiftRead, none, .left)
          | some b => (.reject, some b, .stay)

      -- later true / final false: erased unary markers are blanks, followed by
      -- the traversed Boolean pref, followed by the witness marker blank
      | .seekBlanks =>
          match symbol with
          | none => (.seekBlanks, none, .left)
          | some b => (.seekBits, some b, .left)
      | .seekBits =>
          match symbol with
          | some b => (.seekBits, some b, .left)
          | none => (.shiftRead, none, .left)

      -- move marker one witness cell deeper
      | .shiftRead =>
          match symbol with
          | some false => (.carryFalse, none, .right)
          | some true => (.carryTrue, none, .right)
          | none => (.reject, none, .stay)
      | .carryFalse => (.returnFromMarker, some false, .left)
      | .carryTrue => (.returnFromMarker, some true, .left)

      -- return from the moved marker to the next unary symbol
      | .returnFromMarker =>
          match symbol with
          | none => (.returnBits, none, .right)
          | some b => (.reject, some b, .stay)
      | .returnBits =>
          match symbol with
          | some b => (.returnBits, some b, .right)
          | none => (.returnBlanks, none, .right)
      | .returnBlanks =>
          match symbol with
          | none => (.returnBlanks, none, .right)
          | some b => (.indexSome, some b, .stay)

      -- zero-index final read
      | .finalZeroSep =>
          match symbol with
          | none => (.finalZeroRead, none, .left)
          | some b => (.reject, some b, .stay)
      | .finalZeroRead =>
          match symbol with
          | some false => (.finalZeroBackFalse, some false, .right)
          | some true => (.finalZeroBackTrue, some true, .right)
          | none => (.reject, none, .stay)
      | .finalZeroBackFalse =>
          match symbol with
          | none => (.finalZeroTermFalse, none, .right)
          | some b => (.reject, some b, .stay)
      | .finalZeroBackTrue =>
          match symbol with
          | none => (.finalZeroTermTrue, none, .right)
          | some b => (.reject, some b, .stay)
      | .finalZeroTermFalse =>
          match symbol with
          | some false => (.haltFalse, none, .right)
          | some true => (.reject, some true, .stay)
          | none => (.reject, none, .stay)
      | .finalZeroTermTrue =>
          match symbol with
          | some false => (.haltTrue, none, .right)
          | some true => (.reject, some true, .stay)
          | none => (.reject, none, .stay)

      -- nonzero final read: reach the moved marker
      | .finalSeekBlanks =>
          match symbol with
          | none => (.finalSeekBlanks, none, .left)
          | some b => (.finalSeekBits, some b, .left)
      | .finalSeekBits =>
          match symbol with
          | some b => (.finalSeekBits, some b, .left)
          | none => (.finalRead, none, .left)
      | .finalRead =>
          match symbol with
          | some false => (.selectedFalse, some false, .right)
          | some true => (.selectedTrue, some true, .right)
          | none => (.reject, none, .stay)
      | .selectedFalse =>
          match symbol with
          | none => (.rewindInspectFalse, none, .right)
          | some b => (.reject, some b, .stay)
      | .selectedTrue =>
          match symbol with
          | none => (.rewindInspectTrue, none, .right)
          | some b => (.reject, some b, .stay)

      -- restore traversed witness pref by moving the marker right
      | .rewindInspectFalse =>
          match symbol with
          | some false => (.rewindCarryFF, none, .left)
          | some true => (.rewindCarryFT, none, .left)
          | none => (.cleanupFalse, none, .right)
      | .rewindInspectTrue =>
          match symbol with
          | some false => (.rewindCarryTF, none, .left)
          | some true => (.rewindCarryTT, none, .left)
          | none => (.cleanupTrue, none, .right)
      | .rewindCarryFF => (.rewindAtMarkerFalse, some false, .right)
      | .rewindCarryFT => (.rewindAtMarkerFalse, some true, .right)
      | .rewindCarryTF => (.rewindAtMarkerTrue, some false, .right)
      | .rewindCarryTT => (.rewindAtMarkerTrue, some true, .right)
      | .rewindAtMarkerFalse =>
          match symbol with
          | none => (.rewindInspectFalse, none, .right)
          | some b => (.reject, some b, .stay)
      | .rewindAtMarkerTrue =>
          match symbol with
          | none => (.rewindInspectTrue, none, .right)
          | some b => (.reject, some b, .stay)

      -- consume erased unary region and its false terminator
      | .cleanupFalse =>
          match symbol with
          | none => (.cleanupFalse, none, .right)
          | some false => (.haltFalse, none, .right)
          | some true => (.reject, some true, .stay)
      | .cleanupTrue =>
          match symbol with
          | none => (.cleanupTrue, none, .right)
          | some false => (.haltTrue, none, .right)
          | some true => (.reject, some true, .stay)

      | .haltFalse => (.haltFalse, symbol, .stay)
      | .haltTrue => (.haltTrue, symbol, .stay)
      | .reject => (.reject, symbol, .stay)
    halting := fun q =>
      match q with
      | .haltFalse => true
      | .haltTrue => true
      | .reject => true
      | _ => false }

@[simp] theorem preservingUnaryReadMachine_blank :
    preservingUnaryReadMachine.blank = none := rfl

@[simp] theorem preservingUnaryReadMachine_initial :
    preservingUnaryReadMachine.initial = .index0 := rfl

def preservingReadAccepting : PreservingReadState → Bool
  | .haltTrue => true
  | _ => false


/-- Canonical loop configuration after at least one unary true has already
advanced the witness marker.  `pref` is the traversed witness pref and
therefore has the same length as the erased unary-true region. -/
def indexSomeConfig
    (pref suffix : BitString) (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match encodeNat n with
  | [] =>
      { state := .reject
        tape :=
          { left :=
              List.replicate pref.length none ++
                pref.map some ++ none :: suffix.map some
            head := none
            right := [] } }
  | bit :: rest =>
      { state := .indexSome
        tape :=
          { left :=
              List.replicate pref.length none ++
                pref.map some ++ none :: suffix.map some
            head := some bit
            right := rest.map some } }

@[simp] theorem indexSomeConfig_state
    (pref suffix : BitString) (n : Nat) :
    (indexSomeConfig pref suffix n).state = .indexSome := by
  cases n <;> rfl

/-- The first unary true establishes the general loop invariant in exactly
eight physical steps.  It erases one unary marker, moves the unique witness
marker across the first witness bit, and returns to the next unary symbol. -/
theorem preservingRead_first_true_cycle
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 8
      { state := preservingUnaryReadMachine.initial
        tape := witnessReadTape (b :: tail) (n + 1) } =
      indexSomeConfig [b] tail n := by
  cases b <;> cases n <;>
    simp [preservingUnaryReadMachine, witnessReadTape, indexSomeConfig,
      encodeNat, TM.run, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

/-- Exact final tape for zero index: the witness is unchanged; the unary false
terminator is erased and the original witness separator remains blank. -/
def zeroDoneTape (witness : BitString) : Tape (Option Bool) :=
  { left := none :: none :: witness.map some
    head := none
    right := [] }

theorem preservingRead_zero_run_five
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run 5
      { state := preservingUnaryReadMachine.initial
        tape := witnessReadTape (b :: tail) 0 } =
      { state := if b then .haltTrue else .haltFalse
        tape := zeroDoneTape (b :: tail) } := by
  cases b <;>
    simp [preservingUnaryReadMachine, witnessReadTape, encodeNat,
      zeroDoneTape, TM.run, TM.step, Tape.write, Tape.move]

theorem preservingRead_zero_preserves_witness
    (b : Bool) (tail : BitString) :
    (preservingUnaryReadMachine.run 5
      { state := preservingUnaryReadMachine.initial
        tape := witnessReadTape (b :: tail) 0 }).tape =
      zeroDoneTape (b :: tail) := by
  rw [preservingRead_zero_run_five]

theorem preservingRead_zero_correct
    (b : Bool) (tail : BitString) :
    preservingReadAccepting
      (preservingUnaryReadMachine.run 5
        { state := preservingUnaryReadMachine.initial
          tape := witnessReadTape (b :: tail) 0 }).state = b := by
  rw [preservingRead_zero_run_five]
  cases b <;> rfl

#print axioms MCore.Real.P01PreservingUnaryWitnessMachine.preservingRead_first_true_cycle
#print axioms MCore.Real.P01PreservingUnaryWitnessMachine.preservingRead_zero_run_five
#print axioms MCore.Real.P01PreservingUnaryWitnessMachine.preservingRead_zero_preserves_witness
#print axioms MCore.Real.P01PreservingUnaryWitnessMachine.preservingRead_zero_correct

end P01PreservingUnaryWitnessMachine
end Real
end MCore
