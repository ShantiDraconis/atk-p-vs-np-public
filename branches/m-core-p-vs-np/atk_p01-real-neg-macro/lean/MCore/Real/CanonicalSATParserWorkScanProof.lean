import MCore.Real.CanonicalSATParserHeadProof
import MCore.Real.CanonicalSATSlotLogMachine

namespace MCore
namespace Real
namespace CanonicalSATParserWorkScanProof

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserHeadProof
open CanonicalSATSlotLog
open CanonicalSATSlotLogMachine

/-- Source-preserving scan configuration used by LEAF/BINARY seek states. -/
def sourceScanConfig
    (q : Fin 25)
    (left : List (Option Bool))
    (unread : BitString)
    (log : SlotLog) :
    Configuration (Fin 25) (Option Bool) :=
  match unread with
  | [] =>
      { state := q
        tape := { left := left, head := none, right := log.map some } }
  | b :: bs =>
      { state := q
        tape :=
          { left := left
            head := some b
            right := bs.map some ++ none :: log.map some } }

@[simp] theorem sourceScanConfig_state
    (q : Fin 25)
    (left : List (Option Bool))
    (unread : BitString)
    (log : SlotLog) :
    (sourceScanConfig q left unread log).state = q := by
  cases unread <;> rfl

@[simp] theorem not_halted_11 :
    parserMachine.halting (11 : Fin 25) = false := by decide
@[simp] theorem not_halted_12 :
    parserMachine.halting (12 : Fin 25) = false := by decide
@[simp] theorem not_halted_18 :
    parserMachine.halting (18 : Fin 25) = false := by decide
@[simp] theorem not_halted_19 :
    parserMachine.halting (19 : Fin 25) = false := by decide

theorem leaf_seek_step_cons
    (left : List (Option Bool))
    (b : Bool)
    (bs : BitString)
    (log : SlotLog) :
    parserMachine.step (sourceScanConfig 11 left (b :: bs) log) =
      sourceScanConfig 11 (some b :: left) bs log := by
  cases bs <;>
    simp [parserMachine, sourceScanConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem binary_seek_step_cons
    (left : List (Option Bool))
    (b : Bool)
    (bs : BitString)
    (log : SlotLog) :
    parserMachine.step (sourceScanConfig 18 left (b :: bs) log) =
      sourceScanConfig 18 (some b :: left) bs log := by
  cases bs <;>
    simp [parserMachine, sourceScanConfig, TM.step, Tape.write, Tape.move,
      List.append_assoc]

/-- Cross the delimiter and enter the first work-log cell. -/
theorem leaf_cross_delimiter
    (left : List (Option Bool))
    (log : SlotLog) :
    parserMachine.step (sourceScanConfig 11 left [] log) =
      workConfig (n := 25) 12 (none :: left) log := by
  cases log <;>
    simp [parserMachine, sourceScanConfig, workConfig,
      TM.step, Tape.write, Tape.move]

theorem binary_cross_delimiter
    (left : List (Option Bool))
    (log : SlotLog) :
    parserMachine.step (sourceScanConfig 18 left [] log) =
      workConfig (n := 25) 19 (none :: left) log := by
  cases log <;>
    simp [parserMachine, sourceScanConfig, workConfig,
      TM.step, Tape.write, Tape.move]

/-- Seek through all unread source bits and cross exactly one blank delimiter. -/
theorem leaf_seek_to_work
    (left : List (Option Bool))
    (unread : BitString)
    (log : SlotLog) :
    parserMachine.run (unread.length + 1)
      (sourceScanConfig 11 left unread log) =
    workConfig (n := 25) 12
      (none :: unread.reverse.map some ++ left) log := by
  induction unread generalizing left with
  | nil =>
      simpa using leaf_cross_delimiter left log
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
      rw [TM.run, sourceScanConfig_state, not_halted_11]
      rw [leaf_seek_step_cons]
      rw [ih (some b :: left)]
      congr 2
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem binary_seek_to_work
    (left : List (Option Bool))
    (unread : BitString)
    (log : SlotLog) :
    parserMachine.run (unread.length + 1)
      (sourceScanConfig 18 left unread log) =
    workConfig (n := 25) 19
      (none :: unread.reverse.map some ++ left) log := by
  induction unread generalizing left with
  | nil =>
      simpa using binary_cross_delimiter left log
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
      rw [TM.run, sourceScanConfig_state, not_halted_18]
      rw [binary_seek_step_cons]
      rw [ih (some b :: left)]
      congr 2
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Physical configuration after scanning the work log to its end and moving
one cell left. -/
def afterEndMoveLeft
    (q : Fin 25)
    (pref : List (Option Bool))
    (log : SlotLog)
    (writtenEnd : Option Bool) :
    Configuration (Fin 25) (Option Bool) :=
  { state := q
    tape :=
      Tape.move none .left
        { left := (log.map some).reverse ++ pref
          head := writtenEnd
          right := [] } }

theorem leaf_log_scan_step_cons
    (pref : List (Option Bool))
    (b : Bool)
    (bs : SlotLog) :
    parserMachine.step (workConfig (n := 25) 12 pref (b :: bs)) =
      workConfig (n := 25) 12 (some b :: pref) bs := by
  cases bs <;>
    simp [parserMachine, workConfig, TM.step, Tape.write, Tape.move]

theorem leaf_log_end_step
    (pref : List (Option Bool)) :
    parserMachine.step (workConfig (n := 25) 12 pref []) =
      afterEndMoveLeft 13 pref [] none := by
  simp [parserMachine, workConfig, afterEndMoveLeft,
    TM.step, Tape.write, Tape.move]

/-- State 12 scans the full work log; the final blank step enters pop-search. -/
theorem leaf_scan_log_to_pop
    (pref : List (Option Bool))
    (log : SlotLog) :
    parserMachine.run (log.length + 1)
      (workConfig (n := 25) 12 pref log) =
    afterEndMoveLeft 13 pref log none := by
  induction log generalizing pref with
  | nil =>
      simpa using leaf_log_end_step pref
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
      rw [TM.run, workConfig_state, not_halted_12]
      rw [leaf_log_scan_step_cons]
      rw [ih (some b :: pref)]
      simp [afterEndMoveLeft, List.reverse_cons, List.map_append,
        List.append_assoc]

theorem binary_log_scan_step_cons
    (pref : List (Option Bool))
    (b : Bool)
    (bs : SlotLog) :
    parserMachine.step (workConfig (n := 25) 19 pref (b :: bs)) =
      workConfig (n := 25) 19 (some b :: pref) bs := by
  cases bs <;>
    simp [parserMachine, workConfig, TM.step, Tape.write, Tape.move]

/-- Binary end step appends one active slot and starts returning left. -/
theorem binary_scan_log_to_return
    (pref : List (Option Bool))
    (log : SlotLog) :
    parserMachine.run (log.length + 1)
      (workConfig (n := 25) 19 pref log) =
    afterEndMoveLeft 20 pref log (some true) := by
  induction log generalizing pref with
  | nil =>
      simp [TM.run, workConfig, parserMachine, afterEndMoveLeft,
        TM.step, Tape.write, Tape.move]
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
      rw [TM.run, workConfig_state, not_halted_19]
      rw [binary_log_scan_step_cons]
      rw [ih (some b :: pref)]
      simp [afterEndMoveLeft, List.reverse_cons, List.map_append,
        List.append_assoc]

#print axioms MCore.Real.CanonicalSATParserWorkScanProof.leaf_seek_to_work
#print axioms MCore.Real.CanonicalSATParserWorkScanProof.binary_seek_to_work
#print axioms MCore.Real.CanonicalSATParserWorkScanProof.leaf_scan_log_to_pop
#print axioms MCore.Real.CanonicalSATParserWorkScanProof.binary_scan_log_to_return

end CanonicalSATParserWorkScanProof
end Real
end MCore
