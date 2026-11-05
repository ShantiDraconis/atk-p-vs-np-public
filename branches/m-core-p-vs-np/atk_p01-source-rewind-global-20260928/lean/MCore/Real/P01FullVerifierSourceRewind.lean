import MCore.Real.P01FullVerifierPhysicalShuttles

namespace MCore
namespace Real
namespace P01FullVerifierSourceRewind

open CanonicalFinalProof
open P01FullVerifierPhysicalShuttles

/-- Three-state local macro:
0 enters the source from the source-end blank;
1 scans left across source bits until the witness/source separator blank;
2 halts after moving right to the first source cell (or source-end blank if empty).
-/
abbrev RewindState := Fin 3

def enterSource : RewindState := 0
def scanLeft : RewindState := 1
def rewindHalt : RewindState := 2

def sourceRewindMachine : TM RewindState (Option Bool) :=
  { initial := enterSource
    blank := none
    transition := fun q symbol =>
      if q = enterSource then
        (scanLeft, symbol, .left)
      else if q = scanLeft then
        match symbol with
        | some b => (scanLeft, some b, .left)
        | none => (rewindHalt, none, .right)
      else
        (rewindHalt, symbol, .stay)
    halting := fun q => q == rewindHalt }

@[simp] theorem sourceRewindMachine_blank :
    sourceRewindMachine.blank = none := rfl

@[simp] theorem enterSource_not_halted :
    sourceRewindMachine.halting enterSource = false := by decide

@[simp] theorem scanLeft_not_halted :
    sourceRewindMachine.halting scanLeft = false := by decide

@[simp] theorem rewindHalt_halted :
    sourceRewindMachine.halting rewindHalt = true := by decide

def sourceRewindTimeBound : TimeBound :=
  fun n => n + 2

theorem sourceRewindTimeBound_poly :
    PolynomialTimeBound sourceRewindTimeBound := by
  refine ⟨2, 1, ?_⟩
  intro n
  simp [sourceRewindTimeBound]
  omega

/-- First physical step from source-end enters the last source cell, or the
separator itself when the source is empty. -/
theorem sourceRewind_enter_step
    (witness source : BitString) :
    sourceRewindMachine.step
      { state := enterSource, tape := sourceEndTape witness source } =
      { state := scanLeft,
        tape := Tape.move none .left (sourceEndTape witness source) } := by
  simp [sourceRewindMachine, enterSource, scanLeft, TM.step, Tape.write]

/-- Once the separator blank is under the head, one legal right move reaches
the source-start side and enters the halting state. -/
theorem sourceRewind_separator_step
    (t : Tape (Option Bool))
    (hhead : t.head = none) :
    sourceRewindMachine.step { state := scanLeft, tape := t } =
      { state := rewindHalt, tape := Tape.move none .right t } := by
  cases t with
  | mk left head right =>
      cases head with
      | none =>
          simp [sourceRewindMachine, scanLeft, rewindHalt, enterSource,
            TM.step, Tape.write]
      | some b =>
          simp at hhead

/-- Source-end layout parameterized directly by the nearest-first reversed
source word. This is definitionally the existing sourceEndTape when
`revSource = source.reverse`. -/
def sourceEndTapeFromRev
    (witness revSource : BitString) : Tape (Option Bool) :=
  { left := revSource.map some ++ none :: witness.map some
    head := none
    right := [] }

/-- State-1 scanning configuration. `revSource` is precisely the remaining
nearest-first source segment still to cross. -/
def scanRevConfig
    (witness revSource : BitString)
    (right : List (Option Bool)) :
    Configuration RewindState (Option Bool) :=
  match revSource with
  | [] =>
      { state := scanLeft
        tape := { left := witness.map some, head := none, right := right } }
  | b :: bs =>
      { state := scanLeft
        tape :=
          { left := bs.map some ++ none :: witness.map some
            head := some b
            right := right } }

@[simp] theorem scanRevConfig_state
    (witness revSource : BitString)
    (right : List (Option Bool)) :
    (scanRevConfig witness revSource right).state = scanLeft := by
  cases revSource <;> rfl

theorem enter_from_rev_step
    (witness revSource : BitString) :
    sourceRewindMachine.step
      { state := enterSource, tape := sourceEndTapeFromRev witness revSource } =
      scanRevConfig witness revSource [none] := by
  cases revSource <;>
    simp [sourceEndTapeFromRev, scanRevConfig, sourceRewindMachine,
      enterSource, scanLeft, TM.step, Tape.write, Tape.move]

theorem scanRev_step_cons
    (witness : BitString) (b : Bool) (bs : BitString)
    (right : List (Option Bool)) :
    sourceRewindMachine.step
      (scanRevConfig witness (b :: bs) right) =
      scanRevConfig witness bs (some b :: right) := by
  cases bs <;>
    simp [scanRevConfig, sourceRewindMachine, enterSource, scanLeft,
      rewindHalt, TM.step, Tape.write, Tape.move, List.append_assoc]

theorem scanRev_step_nil
    (witness : BitString)
    (right : List (Option Bool)) :
    sourceRewindMachine.step
      (scanRevConfig witness [] right) =
      { state := rewindHalt
        tape := Tape.move none .right
          { left := witness.map some, head := none, right := right } } := by
  simp [scanRevConfig, sourceRewindMachine, enterSource, scanLeft,
    rewindHalt, TM.step, Tape.write]

/-- Global execution of the left scan. After crossing exactly the remaining
source segment and its separator, the machine is halted one cell to the right
of that separator. -/
theorem scanRev_run
    (witness revSource : BitString)
    (right : List (Option Bool)) :
    sourceRewindMachine.run (revSource.length + 1)
      (scanRevConfig witness revSource right) =
      { state := rewindHalt
        tape := Tape.move none .right
          { left := witness.map some
            head := none
            right := revSource.reverse.map some ++ right } } := by
  induction revSource generalizing right with
  | nil =>
      simp [scanRevConfig, TM.run, sourceRewindMachine, enterSource,
        scanLeft, rewindHalt, TM.step, Tape.write, Tape.move]
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show Nat.succ bs.length + 1 = (bs.length + 1) + 1 by omega]
      rw [TM.run, scanRevConfig_state, scanLeft_not_halted]
      rw [scanRev_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem sourceRewind_run_from_rev
    (witness revSource : BitString) :
    sourceRewindMachine.run (revSource.length + 2)
      { state := enterSource, tape := sourceEndTapeFromRev witness revSource } =
      { state := rewindHalt
        tape := Tape.move none .right
          { left := witness.map some
            head := none
            right := revSource.reverse.map some ++ [none] } } := by
  rw [show revSource.length + 2 = (revSource.length + 1) + 1 by omega]
  rw [TM.run, enterSource_not_halted]
  rw [enter_from_rev_step]
  exact scanRev_run witness revSource [none]

/-- Complete source rewind from the certified source-end layout. -/
theorem sourceRewind_run
    (witness source : BitString) :
    sourceRewindMachine.run (source.length + 2)
      { state := enterSource, tape := sourceEndTape witness source } =
      { state := rewindHalt
        tape := Tape.move none .right
          { left := witness.map some
            head := none
            right := source.map some ++ [none] } } := by
  simpa [sourceEndTapeFromRev, sourceEndTape] using
    (sourceRewind_run_from_rev witness source.reverse)

/-- Every canonical circuit encoding is nonempty, so this is the verifier
entry shape used downstream: rewind returns exactly to preparedTape. -/
theorem sourceRewind_run_prepared_nonempty
    (witness : BitString) (b : Bool) (bs : BitString) :
    sourceRewindMachine.run ((b :: bs).length + 2)
      { state := enterSource, tape := sourceEndTape witness (b :: bs) } =
      { state := rewindHalt, tape := P01WitnessPreservingPrep.preparedTape witness (b :: bs) } := by
  rw [sourceRewind_run]
  simp [P01WitnessPreservingPrep.preparedTape, Tape.move, List.map_append, List.append_assoc]

theorem sourceRewind_halts_nonempty
    (witness : BitString) (b : Bool) (bs : BitString) :
    sourceRewindMachine.HaltsWithin ((b :: bs).length + 2)
      { state := enterSource, tape := sourceEndTape witness (b :: bs) } := by
  unfold TM.HaltsWithin
  rw [sourceRewind_run_prepared_nonempty]
  exact rewindHalt_halted

#print axioms MCore.Real.P01FullVerifierSourceRewind.scanRev_run
#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_run
#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_run_prepared_nonempty
#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_halts_nonempty

#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewindTimeBound_poly
#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_enter_step
#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_separator_step

end P01FullVerifierSourceRewind
end Real
end MCore
