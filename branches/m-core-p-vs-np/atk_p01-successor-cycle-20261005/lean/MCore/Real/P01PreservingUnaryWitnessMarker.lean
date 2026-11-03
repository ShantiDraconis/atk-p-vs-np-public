import MCore.Real.P01EvalTagPhysicalRefinement
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PreservingUnaryWitnessMarker

open CanonicalFinalProof
open MachineRunLemmas

/-!
# Reversible witness marker primitive

The old indexed reader used erased witness cells as its counter.  That cannot
support repeated variable occurrences.  This module isolates the replacement
primitive: a blank marker moves through the witness one cell at a time while
preserving every Boolean symbol, and a second fixed-control machine reverses
the move exactly.

No index is stored in finite control.  The future unary driver only has to
invoke these constant-size primitives once per unary marker and then rewind
the same number of times while consuming those markers.
-/

inductive MarkerAdvanceState where
  | start
  | read
  | carryFalse
  | carryTrue
  | halt
  | reject
  deriving DecidableEq, Repr

/-- Starting on a blank immediately before a witness bit, swap the blank with
that bit.  The Boolean is held only for one transition in finite control. -/
def markerAdvanceMachine : TM MarkerAdvanceState (Option Bool) :=
  { initial := .start
    blank := none
    transition := fun q symbol =>
      match q with
      | .start =>
          match symbol with
          | none => (.read, none, .right)
          | some b => (.reject, some b, .stay)
      | .read =>
          match symbol with
          | some false => (.carryFalse, none, .left)
          | some true => (.carryTrue, none, .left)
          | none => (.reject, none, .stay)
      | .carryFalse => (.halt, some false, .right)
      | .carryTrue => (.halt, some true, .right)
      | .halt => (.halt, symbol, .stay)
      | .reject => (.reject, symbol, .stay)
    halting := fun q =>
      match q with
      | .halt => true
      | .reject => true
      | _ => false }

inductive MarkerRewindState where
  | start
  | read
  | carryFalse
  | carryTrue
  | halt
  | reject
  deriving DecidableEq, Repr

/-- Inverse local operation.  Starting on the blank immediately after the last
advanced witness bit, swap it left across that bit and halt on the restored
blank marker. -/
def markerRewindMachine : TM MarkerRewindState (Option Bool) :=
  { initial := .start
    blank := none
    transition := fun q symbol =>
      match q with
      | .start =>
          match symbol with
          | none => (.read, none, .left)
          | some b => (.reject, some b, .stay)
      | .read =>
          match symbol with
          | some false => (.carryFalse, none, .right)
          | some true => (.carryTrue, none, .right)
          | none => (.reject, none, .stay)
      | .carryFalse => (.halt, some false, .left)
      | .carryTrue => (.halt, some true, .left)
      | .halt => (.halt, symbol, .stay)
      | .reject => (.reject, symbol, .stay)
    halting := fun q =>
      match q with
      | .halt => true
      | .reject => true
      | _ => false }

@[simp] theorem markerAdvance_start_not_halting :
    markerAdvanceMachine.halting .start = false := rfl

@[simp] theorem markerAdvance_read_not_halting :
    markerAdvanceMachine.halting .read = false := rfl

@[simp] theorem markerAdvance_carryFalse_not_halting :
    markerAdvanceMachine.halting .carryFalse = false := rfl

@[simp] theorem markerAdvance_carryTrue_not_halting :
    markerAdvanceMachine.halting .carryTrue = false := rfl

@[simp] theorem markerRewind_start_not_halting :
    markerRewindMachine.halting .start = false := rfl

@[simp] theorem markerRewind_read_not_halting :
    markerRewindMachine.halting .read = false := rfl

@[simp] theorem markerRewind_carryFalse_not_halting :
    markerRewindMachine.halting .carryFalse = false := rfl

@[simp] theorem markerRewind_carryTrue_not_halting :
    markerRewindMachine.halting .carryTrue = false := rfl

/-- Canonical local view of a marker immediately before a nonempty witness
suffix.  `left` may contain the source side and an already traversed witness
prefix; the primitive does not inspect it. -/
def markerBefore
    (left : List (Option Bool)) (b : Bool)
    (tail : List (Option Bool)) : Tape (Option Bool) :=
  { left := left, head := none, right := some b :: tail }

/-- After one advance the same bit is on the left of the marker. -/
def markerAfter
    (left : List (Option Bool)) (b : Bool)
    (tail : List (Option Bool)) : Tape (Option Bool) :=
  { left := some b :: left, head := none, right := tail }

theorem markerAdvance_run_three
    (left : List (Option Bool)) (b : Bool)
    (tail : List (Option Bool)) :
    markerAdvanceMachine.run 3
      { state := markerAdvanceMachine.initial
        tape := markerBefore left b tail } =
      { state := .halt
        tape := markerAfter left b tail } := by
  cases b <;>
    simp [markerAdvanceMachine, markerBefore, markerAfter,
      TM.run, TM.step, Tape.write, Tape.move]

theorem markerRewind_run_three
    (left : List (Option Bool)) (b : Bool)
    (tail : List (Option Bool)) :
    markerRewindMachine.run 3
      { state := markerRewindMachine.initial
        tape := markerAfter left b tail } =
      { state := .halt
        tape := markerBefore left b tail } := by
  cases b <;>
    simp [markerRewindMachine, markerBefore, markerAfter,
      TM.run, TM.step, Tape.write, Tape.move]

/-- Exact local reversibility: the advance and rewind machines induce inverse
tape transformations. -/
theorem marker_tape_roundTrip
    (left : List (Option Bool)) (b : Bool)
    (tail : List (Option Bool)) :
    (markerRewindMachine.run 3
      { state := markerRewindMachine.initial
        tape :=
          (markerAdvanceMachine.run 3
            { state := markerAdvanceMachine.initial
              tape := markerBefore left b tail }).tape }).tape =
      markerBefore left b tail := by
  rw [markerAdvance_run_three]
  rw [markerRewind_run_three]

/-- The advance operation exposes the next witness cell without deleting any
Boolean payload. -/
theorem markerAdvance_preserves_payload
    (left : List (Option Bool)) (b : Bool)
    (tail : List (Option Bool)) :
    let final :=
      markerAdvanceMachine.run 3
        { state := markerAdvanceMachine.initial
          tape := markerBefore left b tail }
    final.tape.left = some b :: left ∧
      final.tape.head = none ∧
      final.tape.right = tail := by
  rw [markerAdvance_run_three]
  simp [markerAfter]

/-- Both local machines have constant cost.  A unary driver invoking them once
per marker therefore contributes linear local work; shuttle distance is the
only remaining global cost term. -/
def markerLocalTimeBound (n : Nat) : Nat := 6 * n

theorem markerLocalTimeBound_linear (n : Nat) :
    markerLocalTimeBound n = 6 * n := rfl

#print axioms MCore.Real.P01PreservingUnaryWitnessMarker.markerAdvance_run_three
#print axioms MCore.Real.P01PreservingUnaryWitnessMarker.markerRewind_run_three
#print axioms MCore.Real.P01PreservingUnaryWitnessMarker.marker_tape_roundTrip
#print axioms MCore.Real.P01PreservingUnaryWitnessMarker.markerAdvance_preserves_payload

end P01PreservingUnaryWitnessMarker
end Real
end MCore
