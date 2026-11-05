import MCore.Real.P01FullVerifierSourceRewind

namespace MCore
namespace Real
namespace P01SourceRewindGlobal

open CanonicalFinalProof
open P01WitnessPreservingPrep
open P01FullVerifierPhysicalShuttles
open P01FullVerifierSourceRewind

/-- Exact intermediate configuration while the rewind machine scans the
source from right to left.  `rev` contains the unread source symbols in
right-to-left order; `right` contains the already crossed cells. -/
def rewindScanConfig
    (witness : BitString)
    (rev : List Bool)
    (right : List (Option Bool)) :
    Configuration RewindState (Option Bool) :=
  match rev with
  | [] =>
      { state := scanLeft
        tape :=
          { left := witness.map some
            head := none
            right := right } }
  | b :: bs =>
      { state := scanLeft
        tape :=
          { left := bs.map some ++ none :: witness.map some
            head := some b
            right := right } }

@[simp] theorem rewindScanConfig_state
    (witness rev : BitString)
    (right : List (Option Bool)) :
    (rewindScanConfig witness rev right).state = scanLeft := by
  cases rev <;> rfl

/-- One scanning step consumes exactly the current reversed-source bit. -/
theorem rewindScanConfig_step_cons
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (right : List (Option Bool)) :
    sourceRewindMachine.step
      (rewindScanConfig witness (b :: bs) right) =
      rewindScanConfig witness bs (some b :: right) := by
  cases bs <;>
    simp [rewindScanConfig, sourceRewindMachine, TM.step,
      scanLeft, enterSource, rewindHalt, Tape.write, Tape.move]

/-- Scanning a finite reversed source reaches the witness/source separator and
then performs the certified one-cell right step.  This is a genuine global
execution theorem for the concrete three-state rewind TM. -/
theorem rewindScanConfig_run
    (witness rev : BitString)
    (right : List (Option Bool)) :
    sourceRewindMachine.run (rev.length + 1)
      (rewindScanConfig witness rev right) =
      { state := rewindHalt
        tape := Tape.move none .right
          { left := witness.map some
            head := none
            right := rev.reverse.map some ++ right } } := by
  induction rev generalizing right with
  | nil =>
      have hstep :=
        sourceRewind_separator_step
          ({ left := witness.map some
             head := none
             right := right } : Tape (Option Bool))
          rfl
      simpa [rewindScanConfig, TM.run, scanLeft_not_halted] using hstep
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
      rw [TM.run]
      have hnot :
          ¬ sourceRewindMachine.halting
              (rewindScanConfig witness (b :: bs) right).state = true := by
        simp [rewindScanConfig_state, scanLeft_not_halted]
      rw [if_neg hnot]
      rw [rewindScanConfig_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- The first left move from a nonempty source-end layout is exactly the
intermediate reversed-source configuration. -/
theorem enterSource_step_eq_rewindScanConfig
    (witness : BitString)
    (b : Bool) (bs : BitString) :
    ({ state := scanLeft
       tape := Tape.move none .left (sourceEndTape witness (b :: bs)) } :
      Configuration RewindState (Option Bool)) =
      rewindScanConfig witness (b :: bs).reverse [none] := by
  cases hrev : bs.reverse with
  | nil =>
      simp [sourceEndTape, rewindScanConfig, Tape.move,
        List.reverse_cons, List.map_append, hrev]
  | cons x xs =>
      simp [sourceEndTape, rewindScanConfig, Tape.move,
        List.reverse_cons, List.map_append, hrev, List.append_assoc]

/-- For every nonempty canonical source, the concrete rewind TM returns from
the source-end blank to exactly the witness-preserving prepared-tape layout.
The bound is source.length + 2 primitive TM steps. -/
theorem sourceRewind_run_prepared
    (witness : BitString)
    (b : Bool)
    (bs : BitString) :
    sourceRewindMachine.run ((b :: bs).length + 2)
      { state := enterSource
        tape := sourceEndTape witness (b :: bs) } =
      { state := rewindHalt
        tape := preparedTape witness (b :: bs) } := by
  rw [show (b :: bs).length + 2 =
      ((b :: bs).reverse.length + 1) + 1 by simp]
  rw [TM.run]
  have hnot :
      ¬ sourceRewindMachine.halting enterSource = true := by
    simp [enterSource_not_halted]
  rw [if_neg hnot]
  rw [sourceRewind_enter_step]
  rw [enterSource_step_eq_rewindScanConfig]
  rw [rewindScanConfig_run]
  simp [preparedTape, List.map_append, List.append_assoc, Tape.move]

/-- The advertised linear rewind time bound is exact for the nonempty source
run above. -/
theorem sourceRewind_nonempty_halts
    (witness : BitString)
    (b : Bool)
    (bs : BitString) :
    sourceRewindMachine.HaltsWithin
      (sourceRewindTimeBound (b :: bs).length)
      { state := enterSource
        tape := sourceEndTape witness (b :: bs) } := by
  unfold sourceRewindTimeBound TM.HaltsWithin
  rw [sourceRewind_run_prepared]
  exact rewindHalt_halted

#print axioms MCore.Real.P01SourceRewindGlobal.rewindScanConfig_step_cons
#print axioms MCore.Real.P01SourceRewindGlobal.rewindScanConfig_run
#print axioms MCore.Real.P01SourceRewindGlobal.enterSource_step_eq_rewindScanConfig
#print axioms MCore.Real.P01SourceRewindGlobal.sourceRewind_run_prepared
#print axioms MCore.Real.P01SourceRewindGlobal.sourceRewind_nonempty_halts

end P01SourceRewindGlobal
end Real
end MCore
