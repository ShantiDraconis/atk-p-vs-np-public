import MCore.Real.CanonicalSATParserLeafPopProof
import MCore.Real.CanonicalSATSlotLog

namespace MCore
namespace Real
namespace CanonicalSATParserLeafReturnProof

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserLeafPopProof
open CanonicalSATSlotLog

/-- State-14/state-15 left scan after the rightmost active slot has been
converted into a false tombstone. remaining is ordered from the current head
toward the source/work delimiter. -/
def leafCheckConfig
    (q : Fin 25)
    (remaining : SlotLog)
    (sourceLeft right : List (Option Bool)) :
    Configuration (Fin 25) (Option Bool) :=
  match remaining with
  | [] =>
      { state := q
        tape := { left := sourceLeft, head := none, right := right } }
  | b :: bs =>
      { state := q
        tape :=
          { left := bs.map some ++ none :: sourceLeft
            head := some b
            right := right } }

/-- State immediately after state 14/15 crosses the source/work delimiter and
moves one cell left into source input (or a blank if source is exhausted). -/
def leafSourceCheckConfig
    (q : Fin 25)
    (sourceLeft right : List (Option Bool)) :
    Configuration (Fin 25) (Option Bool) :=
  { state := q
    tape :=
      Tape.move none .left
        { left := sourceLeft
          head := none
          right := right } }

@[simp] theorem leafCheckConfig_state
    (q : Fin 25)
    (remaining : SlotLog)
    (sourceLeft right : List (Option Bool)) :
    (leafCheckConfig q remaining sourceLeft right).state = q := by
  cases remaining <;> rfl

@[simp] theorem parser_not_halted_14 :
    parserMachine.halting (14 : Fin 25) = false := by decide

@[simp] theorem parser_not_halted_15 :
    parserMachine.halting (15 : Fin 25) = false := by decide

theorem leaf14_step_false
    (bs : SlotLog)
    (sourceLeft right : List (Option Bool)) :
    parserMachine.step
        (leafCheckConfig 14 (false :: bs) sourceLeft right) =
      leafCheckConfig 14 bs sourceLeft (some false :: right) := by
  cases bs <;>
    simp [leafCheckConfig, parserMachine, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem leaf14_step_true
    (bs : SlotLog)
    (sourceLeft right : List (Option Bool)) :
    parserMachine.step
        (leafCheckConfig 14 (true :: bs) sourceLeft right) =
      leafCheckConfig 15 bs sourceLeft (some true :: right) := by
  cases bs <;>
    simp [leafCheckConfig, parserMachine, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem leaf15_step
    (b : Bool)
    (bs : SlotLog)
    (sourceLeft right : List (Option Bool)) :
    parserMachine.step
        (leafCheckConfig 15 (b :: bs) sourceLeft right) =
      leafCheckConfig 15 bs sourceLeft (some b :: right) := by
  cases b <;> cases bs <;>
    simp [leafCheckConfig, parserMachine, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem leaf14_end_step
    (sourceLeft right : List (Option Bool)) :
    parserMachine.step
        (leafCheckConfig 14 [] sourceLeft right) =
      leafSourceCheckConfig 16 sourceLeft right := by
  simp [leafCheckConfig, leafSourceCheckConfig, parserMachine,
    TM.step, Tape.write, Tape.move]

theorem leaf15_end_step
    (sourceLeft right : List (Option Bool)) :
    parserMachine.step
        (leafCheckConfig 15 [] sourceLeft right) =
      leafSourceCheckConfig 17 sourceLeft right := by
  simp [leafCheckConfig, leafSourceCheckConfig, parserMachine,
    TM.step, Tape.write, Tape.move]

/-- Once one active slot has been observed, state 15 scans all remaining older
cells and reaches state 17 at the source delimiter. -/
theorem leaf15_run
    (remaining : SlotLog)
    (sourceLeft right : List (Option Bool)) :
    parserMachine.run (remaining.length + 1)
        (leafCheckConfig 15 remaining sourceLeft right) =
      leafSourceCheckConfig 17 sourceLeft
        (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil =>
      simpa using leaf15_end_step sourceLeft right
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
      rw [TM.run]
      simp only [leafCheckConfig_state, parser_not_halted_15,
        Bool.false_eq_true, if_false]
      rw [leaf15_step]
      rw [ih (some b :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- If every older work-log cell is false, state 14 never observes another
active slot and reaches state 16. -/
theorem leaf14_all_false_run
    (remaining : SlotLog)
    (sourceLeft right : List (Option Bool))
    (hall : ∀ b ∈ remaining, b = false) :
    parserMachine.run (remaining.length + 1)
        (leafCheckConfig 14 remaining sourceLeft right) =
      leafSourceCheckConfig 16 sourceLeft
        (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil =>
      simpa using leaf14_end_step sourceLeft right
  | cons b bs ih =>
      have hb : b = false := hall b (by simp)
      subst b
      have htail : ∀ x ∈ bs, x = false := by
        intro x hx
        exact hall x (by simp [hx])
      rw [List.length_cons]
      rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
      rw [TM.run]
      simp only [leafCheckConfig_state, parser_not_halted_14,
        Bool.false_eq_true, if_false]
      rw [leaf14_step_false]
      rw [ih (some false :: right) htail]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- If an older active slot exists, state 14 eventually sees the first such
true cell, switches to state 15, and reaches state 17 at the delimiter. -/
theorem leaf14_active_run
    (remaining : SlotLog)
    (sourceLeft right : List (Option Bool))
    (hactive : activeSlots remaining ≠ 0) :
    parserMachine.run (remaining.length + 1)
        (leafCheckConfig 14 remaining sourceLeft right) =
      leafSourceCheckConfig 17 sourceLeft
        (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil =>
      simp [activeSlots] at hactive
  | cons b bs ih =>
      cases b with
      | false =>
          have htail : activeSlots bs ≠ 0 := by
            simpa [activeSlots] using hactive
          rw [List.length_cons]
          rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
          rw [TM.run]
          simp only [leafCheckConfig_state, parser_not_halted_14,
            Bool.false_eq_true, if_false]
          rw [leaf14_step_false]
          rw [ih (some false :: right) htail]
          simp [List.reverse_cons, List.map_append, List.append_assoc]
      | true =>
          rw [List.length_cons]
          rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
          rw [TM.run]
          simp only [leafCheckConfig_state, parser_not_halted_14,
            Bool.false_eq_true, if_false]
          rw [leaf14_step_true]
          rw [leaf15_run bs sourceLeft (some true :: right)]
          simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- The post-pop physical configuration is exactly a state-14 check scan with
the freshly written false tombstone already on the right. -/
theorem leafAfterPop_eq_check
    (remaining : SlotLog)
    (sourceLeft right : List (Option Bool)) :
    leafAfterPopConfig remaining (none :: sourceLeft) right =
      leafCheckConfig 14 remaining sourceLeft (some false :: right) := by
  cases remaining <;>
    simp [leafAfterPopConfig, leafCheckConfig, Tape.move,
      List.append_assoc]

#print axioms MCore.Real.CanonicalSATParserLeafReturnProof.leaf15_run
#print axioms MCore.Real.CanonicalSATParserLeafReturnProof.leaf14_all_false_run
#print axioms MCore.Real.CanonicalSATParserLeafReturnProof.leaf14_active_run
#print axioms MCore.Real.CanonicalSATParserLeafReturnProof.leafAfterPop_eq_check

end CanonicalSATParserLeafReturnProof
end Real
end MCore
