import MCore.Real.P01PreservingUnaryPhysicalAdvance
import MCore.Real.MachineRunLemmas

namespace MCore.Real.P01PreservingUnaryPhysicalFinal

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryPhysicalAdvance
open MachineRunLemmas

/-- Enter the already-certified finalSeekBlanks layout from indexSome on the
unary false terminator. -/
theorem indexSome_zero_to_finalSeekBlanks
    (x : Bool) (xs : BitString)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run 1
      (indexSomeConfig (x :: xs) (b :: tail) 0) =
      finalSeekBlanksConfig xs.length 0 (x :: xs) b tail := by
  simp [indexSomeConfig, finalSeekBlanksConfig, preservingUnaryReadMachine,
    encodeNat, TM.run, TM.step, Tape.write, Tape.move,
    List.replicate_succ, List.append_assoc]

def finalReadConfig
    (passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .finalRead
    tape :=
      { left := tail.map some
        head := some b
        right := none :: passedRev.map some ++
          List.replicate blankPad none ++ [some false] } }

theorem finalSeekBits_marker_to_finalRead
    (passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run 1
      (finalSeekBitsConfig [] passedRev blankPad b tail) =
      finalReadConfig passedRev blankPad b tail := by
  simp [finalSeekBitsConfig, finalReadConfig,
    preservingUnaryReadMachine, TM.run, TM.step,
    Tape.write, Tape.move, List.append_assoc]

def selectedConfig
    (selected : Bool) (passedRev : BitString)
    (blankPad : Nat) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := if selected then .selectedTrue else .selectedFalse
    tape :=
      { left := some selected :: tail.map some
        head := none
        right := passedRev.map some ++
          List.replicate blankPad none ++ [some false] } }

theorem finalRead_to_selected
    (passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run 1
      (finalReadConfig passedRev blankPad b tail) =
      selectedConfig b passedRev blankPad tail := by
  cases b <;>
    simp [finalReadConfig, selectedConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

/-- Exact physical nonzero final selection.  The cost is
1 + |xs| + 1 + 1 + |xs| + 1 + 1 = 2*|x::xs| + 3. -/
theorem finalSelect_run
    (x : Bool) (xs : BitString)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run (2 * (x :: xs).length + 3)
      (indexSomeConfig (x :: xs) (b :: tail) 0) =
      selectedConfig b ((x :: xs).reverse) ((x :: xs).length) tail := by
  have h0 := indexSome_zero_to_finalSeekBlanks x xs b tail
  have hb := finalSeekBlanks_run xs.length 0 (x :: xs) b tail
  have he := finalSeekBlanks_zero_step_to_bits x xs xs.length b tail
  have hi := finalSeekBits_entry_step x xs xs.length b tail
  have hs := finalSeekBits_run xs [x] ((x :: xs).length) b tail
  have hm := finalSeekBits_marker_to_finalRead ((x :: xs).reverse)
    ((x :: xs).length) b tail
  have hf := finalRead_to_selected ((x :: xs).reverse)
    ((x :: xs).length) b tail
  rw [show 2 * (x :: xs).length + 3 =
      1 + (xs.length + (1 + (1 + (xs.length + (1 + 1))))) by simp; omega]
  rw [run_add, h0]
  rw [run_add, hb]
  rw [run_add, he]
  rw [run_add, hi]
  rw [run_add, hs]
  simp [List.reverse_cons, List.append_assoc] at *
  rw [run_add, hm]
  exact hf

#print axioms MCore.Real.P01PreservingUnaryPhysicalFinal.indexSome_zero_to_finalSeekBlanks
#print axioms MCore.Real.P01PreservingUnaryPhysicalFinal.finalSeekBits_marker_to_finalRead
#print axioms MCore.Real.P01PreservingUnaryPhysicalFinal.finalRead_to_selected
#print axioms MCore.Real.P01PreservingUnaryPhysicalFinal.finalSelect_run

end MCore.Real.P01PreservingUnaryPhysicalFinal
