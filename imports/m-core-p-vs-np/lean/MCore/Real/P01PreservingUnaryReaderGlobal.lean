import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.P01InputNodePreservingPlan
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PreservingUnaryReaderGlobal

open CanonicalFinalProof
open CanonicalCircuitBits
open P01InputNodePreservingPlan
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas
open P01WitnessIndexedRead

/-!
# Global proof layer for the preserving unary witness reader

This file isolates the only remaining physical-reader proof.  The finite
transition graph is fixed in P01PreservingUnaryWitnessMachine; here we expose
canonical configurations for the forward scan, selected-bit rewind, and final
cleanup.  No new machine or semantic oracle is introduced.
-/

/-- Logical payload conservation used throughout the physical induction. -/
theorem payload_advance_rewind
    (pref : BitString) (b : Bool) (suffix : BitString) :
    witnessPayload pref (b :: suffix) =
      witnessPayload (pref ++ [b]) suffix ∧
    witnessPayload (pref ++ [b]) suffix =
      witnessPayload pref (b :: suffix) := by
  exact ⟨witnessPayload_advance pref b suffix,
    witnessPayload_rewind pref b suffix⟩

/-- The existing first physical cycle establishes the induction entry point. -/
theorem preserving_reader_induction_entry
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 8
      { state := preservingUnaryReadMachine.initial
        tape := witnessReadTape (b :: tail) (n + 1) } =
      indexSomeConfig [b] tail n :=
  preservingRead_first_true_cycle b tail n

/-- Exact selected bit is already determined by the decomposition used by the
rewind proof.  This keeps the forthcoming machine induction tied to the frozen
semantic witness rather than to an unconstrained answer field. -/
theorem selected_bit_from_decomposition
    (witness pref suffix : BitString) (b : Bool) (i : Nat)
    (hw : witness = pref ++ b :: suffix)
    (hlen : pref.length = i) :
    witness.getD i false = b := by
  subst witness
  subst i
  simp [List.getD_eq_getElem?_getD]


/-- One local rewind cycle for a false witness bit.  Keeping the next tape
symbol explicit avoids relying on list head defaults in the global induction. -/
theorem rewind_false_control_cycle
    (left : List (Option Bool)) (b : Bool) (next : Option Bool)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run 3
      { state := .rewindInspectFalse
        tape := { left := none :: left, head := some b,
                  right := next :: right } } =
      { state := .rewindInspectFalse
        tape := { left := none :: some b :: left, head := next,
                  right := right } } := by
  cases b <;>
    simp [preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move]

/-- Same physical cycle while the selected result carried in control is true. -/
theorem rewind_true_bit_cycle
    (left : List (Option Bool)) (next : Option Bool)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run 3
      { state := .rewindInspectTrue
        tape := { left := none :: left, head := some true,
                  right := next :: right } } =
      { state := .rewindInspectTrue
        tape := { left := none :: some true :: left, head := next,
                  right := right } } := by
  simp [preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move]


/-- Rewind a Boolean pref while the selected result carried in finite
control is false.  Every restored witness bit costs exactly three steps. -/
theorem rewind_false_bits
    (left : List (Option Bool)) (pref : BitString)
    (next : Option Bool) (right : List (Option Bool)) :
    preservingUnaryReadMachine.run (3 * pref.length)
      { state := .rewindInspectFalse
        tape := { left := none :: left,
                  head := (pref.map some ++ next :: right).headD next,
                  right := (pref.map some ++ next :: right).tail } } =
      { state := .rewindInspectFalse
        tape := { left := none :: pref.reverse.map some ++ left,
                  head := next, right := right } } := by
  induction pref generalizing left with
  | nil =>
      simp [TM.run]
  | cons b bs =>
      rw [List.length_cons]
      rw [show 3 * (bs.length + 1) = 3 + 3 * bs.length by omega]
      rw [MachineRunLemmas.run_add]
      simp only [List.map_cons, List.cons_append, List.headD_cons, List.tail_cons]
      rw [rewind_false_control_cycle]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        (ih (left := some b :: left))

/-- A three-step rewind cycle preserves a selected true result while restoring
an arbitrary witness bit. -/
theorem rewind_true_control_cycle
    (left : List (Option Bool)) (b : Bool) (next : Option Bool)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run 3
      { state := .rewindInspectTrue
        tape := { left := none :: left, head := some b,
                  right := next :: right } } =
      { state := .rewindInspectTrue
        tape := { left := none :: some b :: left, head := next,
                  right := right } } := by
  cases b <;>
    simp [preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move]

/-- Cleanup consumes one erased unary cell without changing the selected
false result. -/
theorem cleanup_false_blank_step
    (left : List (Option Bool)) (next : Option Bool)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run 1
      { state := .cleanupFalse
        tape := { left := left, head := none, right := next :: right } } =
      { state := .cleanupFalse
        tape := { left := none :: left, head := next, right := right } } := by
  simp [preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move]

/-- Cleanup consumes one erased unary cell without changing the selected
true result. -/
theorem cleanup_true_blank_step
    (left : List (Option Bool)) (next : Option Bool)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run 1
      { state := .cleanupTrue
        tape := { left := left, head := none, right := next :: right } } =
      { state := .cleanupTrue
        tape := { left := none :: left, head := next, right := right } } := by
  simp [preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move]

/-- The final false terminator halts with the selected false result. -/
theorem cleanup_false_terminator
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.run 1
      { state := .cleanupFalse
        tape := { left := left, head := some false, right := right } } =
      { state := .haltFalse
        tape := Tape.move none .right
          { left := left, head := none, right := right } } := by
  simp [preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move]

/-- The final false terminator halts with the selected true result. -/
theorem cleanup_true_terminator
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.run 1
      { state := .cleanupTrue
        tape := { left := left, head := some false, right := right } } =
      { state := .haltTrue
        tape := Tape.move none .right
          { left := left, head := none, right := right } } := by
  simp [preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move]

#print axioms MCore.Real.P01PreservingUnaryReaderGlobal.rewind_true_control_cycle

#print axioms MCore.Real.P01PreservingUnaryReaderGlobal.payload_advance_rewind
#print axioms MCore.Real.P01PreservingUnaryReaderGlobal.preserving_reader_induction_entry
#print axioms MCore.Real.P01PreservingUnaryReaderGlobal.selected_bit_from_decomposition

end P01PreservingUnaryReaderGlobal
end Real
end MCore
