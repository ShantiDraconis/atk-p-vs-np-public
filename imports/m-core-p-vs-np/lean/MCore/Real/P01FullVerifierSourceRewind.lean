import MCore.Real.P01FullVerifierPhysicalShuttles
import MCore.Real.MachineRunLemmas

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

#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewindTimeBound_poly
#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_enter_step
#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_separator_step


/-- Exact scan configuration for the unread reversed source. -/
def rewindScanConfig
    (witness : BitString)
    (remaining : BitString)
    (right : List (Option Bool)) :
    Configuration RewindState (Option Bool) :=
  match remaining with
  | [] =>
      { state := scanLeft,
        tape := { left := witness.map some, head := none, right := right } }
  | b :: bs =>
      { state := scanLeft,
        tape := { left := bs.map some ++ none :: witness.map some,
                  head := some b,
                  right := right } }

@[simp] theorem rewindScanConfig_state
    (witness remaining : BitString)
    (right : List (Option Bool)) :
    (rewindScanConfig witness remaining right).state = scanLeft := by
  cases remaining <;> rfl

theorem rewindScan_step_cons
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (right : List (Option Bool)) :
    sourceRewindMachine.step
      (rewindScanConfig witness (b :: bs) right) =
    rewindScanConfig witness bs (some b :: right) := by
  cases bs <;>
    simp [rewindScanConfig, sourceRewindMachine, enterSource, scanLeft,
      rewindHalt, TM.step, Tape.write, Tape.move, List.append_assoc]

theorem rewind_scan_run
    (witness remaining : BitString)
    (right : List (Option Bool)) :
    sourceRewindMachine.run remaining.length
      (rewindScanConfig witness remaining right) =
    rewindScanConfig witness []
      (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons]
      simp only [TM.run, rewindScanConfig_state, scanLeft_not_halted,
        Bool.false_eq_true, if_false]
      rw [rewindScan_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem sourceRewind_enter_to_scan
    (witness source : BitString) :
    sourceRewindMachine.step
      { state := enterSource, tape := sourceEndTape witness source } =
    rewindScanConfig witness source.reverse [none] := by
  cases h : source.reverse with
  | nil =>
      simp [sourceEndTape, rewindScanConfig, sourceRewindMachine,
        enterSource, scanLeft, TM.step, Tape.write, Tape.move, h]
  | cons b bs =>
      simp [sourceEndTape, rewindScanConfig, sourceRewindMachine,
        enterSource, scanLeft, TM.step, Tape.write, Tape.move, h,
        List.append_assoc]

theorem sourceRewind_run_one_enter
    (witness source : BitString) :
    sourceRewindMachine.run 1
      { state := enterSource, tape := sourceEndTape witness source } =
    rewindScanConfig witness source.reverse [none] := by
  rw [TM.run]
  simp only [enterSource_not_halted, Bool.false_eq_true, if_false]
  exact sourceRewind_enter_to_scan witness source

/-- From a canonical source-end tape, the real rewind TM halts within the
linear bound n+2. -/
theorem sourceRewind_halts_linear
    (witness source : BitString) :
    sourceRewindMachine.HaltsWithin
      (source.length + 2)
      { state := enterSource, tape := sourceEndTape witness source } := by
  unfold TM.HaltsWithin
  rw [show source.length + 2 = 1 + (source.length + 1) by omega]
  rw [MachineRunLemmas.run_add]
  rw [sourceRewind_run_one_enter]
  rw [show source.length + 1 = source.reverse.length + 1 by simp]
  rw [MachineRunLemmas.run_add]
  rw [rewind_scan_run]
  simp [rewindScanConfig, sourceRewindMachine, enterSource, scanLeft,
    rewindHalt, TM.run, TM.step, Tape.write, Tape.move]

#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_halts_linear

end P01FullVerifierSourceRewind
end Real
end MCore
