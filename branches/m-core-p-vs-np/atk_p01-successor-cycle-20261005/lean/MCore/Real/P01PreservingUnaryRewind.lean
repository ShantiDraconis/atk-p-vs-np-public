import MCore.Real.P01PreservingUnaryFinalRead

namespace MCore
namespace Real
namespace P01PreservingUnaryRewind

open CanonicalFinalProof
open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryFinalRead
open MachineRunLemmas

/-- Active rewind state.  remaining is in the physical order encountered by
the head; restored is already reconstructed in logical witness order. -/
def rewindActiveConfig
    (selected x : Bool) (xs restored : BitString) (blanks : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := if selected then .rewindInspectTrue else .rewindInspectFalse
    tape :=
      { left := none :: restored.map some
        head := some x
        right := xs.map some ++ List.replicate blanks none ++ [some false] } }

/-- State after the last traversed witness bit has been restored.  The head is
on the first erased unary blank; blankTail counts the blanks still to its
right before the false terminator. -/
def rewindDoneConfig
    (selected : Bool) (witness : BitString) (blankTail : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := if selected then .rewindInspectTrue else .rewindInspectFalse
    tape :=
      { left := none :: witness.map some
        head := none
        right := List.replicate blankTail none ++ [some false] } }

@[simp] theorem rewindActive_state_false
    (x : Bool) (xs restored : BitString) (blanks : Nat) :
    (rewindActiveConfig false x xs restored blanks).state = .rewindInspectFalse := rfl

@[simp] theorem rewindActive_state_true
    (x : Bool) (xs restored : BitString) (blanks : Nat) :
    (rewindActiveConfig true x xs restored blanks).state = .rewindInspectTrue := rfl

/-- One selected-state step enters the active rewind scanner. -/
theorem selected_to_rewind_active
    (pref : BitString) (b : Bool) (suffix : BitString)
    (hp : pref ≠ []) :
    ∃ x xs,
      pref.reverse = x :: xs ∧
      preservingUnaryReadMachine.run 1 (selectedConfig pref b suffix) =
        rewindActiveConfig b x xs (b :: suffix) pref.length := by
  have hrev : pref.reverse ≠ [] := by
    simpa using hp
  cases h : pref.reverse with
  | nil =>
      exact False.elim (hrev h)
  | cons x xs =>
      refine ⟨x, xs, rfl, ?_⟩
      cases b <;>
        simp [selectedConfig, rewindActiveConfig, h,
          preservingUnaryReadMachine, TM.run, TM.step,
          Tape.write, Tape.move, List.append_assoc]

/-- One nonterminal rewind cell. -/
theorem rewind_one_cell_more
    (selected x y : Bool) (ys restored : BitString) (blanks : Nat) :
    preservingUnaryReadMachine.run 3
      (rewindActiveConfig selected x (y :: ys) restored blanks) =
      rewindActiveConfig selected y ys (x :: restored) blanks := by
  cases selected <;> cases x <;> cases y <;>
    simp [rewindActiveConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move,
      List.append_assoc]

/-- Last rewind cell.  At least one erased unary blank exists for every
reachable nonzero index. -/
theorem rewind_one_cell_last
    (selected x : Bool) (restored : BitString) (blankTail : Nat) :
    preservingUnaryReadMachine.run 3
      (rewindActiveConfig selected x [] restored (blankTail + 1)) =
      rewindDoneConfig selected (x :: restored) blankTail := by
  cases selected <;> cases x <;>
    simp [rewindActiveConfig, rewindDoneConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

/-- Rewind an arbitrary nonempty physical prefix. -/
theorem rewind_all_active
    (selected x : Bool) (xs restored : BitString) (blankTail : Nat) :
    preservingUnaryReadMachine.run (3 * (x :: xs).length)
      (rewindActiveConfig selected x xs restored (blankTail + 1)) =
      rewindDoneConfig selected ((x :: xs).reverse ++ restored) blankTail := by
  induction xs generalizing x restored with
  | nil =>
      simpa using rewind_one_cell_last selected x restored blankTail
  | cons y ys ih =>
      rw [List.length_cons]
      rw [show 3 * (List.length (y :: ys) + 1) =
        3 + 3 * List.length (y :: ys) by omega]
      rw [run_add]
      rw [rewind_one_cell_more]
      have h := ih (x := y) (restored := x :: restored)
      simpa [List.reverse_cons, List.append_assoc] using h

/-- Cleanup scanner after rewindInspect sees the first unary blank. -/
def cleanupScanConfig
    (selected : Bool) (witness : BitString)
    (crossed remaining : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | 0 =>
      { state := if selected then .cleanupTrue else .cleanupFalse
        tape :=
          { left := List.replicate crossed none ++ witness.map some
            head := some false
            right := [] } }
  | k + 1 =>
      { state := if selected then .cleanupTrue else .cleanupFalse
        tape :=
          { left := List.replicate crossed none ++ witness.map some
            head := none
            right := List.replicate k none ++ [some false] } }

@[simp] theorem cleanupScanConfig_state_false
    (witness : BitString) (crossed remaining : Nat) :
    (cleanupScanConfig false witness crossed remaining).state = .cleanupFalse := by
  cases remaining <;> rfl

@[simp] theorem cleanupScanConfig_state_true
    (witness : BitString) (crossed remaining : Nat) :
    (cleanupScanConfig true witness crossed remaining).state = .cleanupTrue := by
  cases remaining <;> rfl

@[simp] theorem preserving_not_halt_cleanupFalse :
    preservingUnaryReadMachine.halting .cleanupFalse = false := rfl

@[simp] theorem preserving_not_halt_cleanupTrue :
    preservingUnaryReadMachine.halting .cleanupTrue = false := rfl

def haltedConfig
    (selected : Bool) (witness : BitString) (leftBlanks : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := if selected then .haltTrue else .haltFalse
    tape :=
      { left := List.replicate leftBlanks none ++ witness.map some
        head := none
        right := [] } }

theorem rewind_done_enter_cleanup
    (selected : Bool) (witness : BitString) (blankTail : Nat) :
    preservingUnaryReadMachine.run 1
      (rewindDoneConfig selected witness blankTail) =
      cleanupScanConfig selected witness 2 blankTail := by
  cases selected <;> cases blankTail <;>
    simp [rewindDoneConfig, cleanupScanConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

/-- Cleanup crosses every remaining blank and then erases the false
terminator. -/
theorem cleanup_scan_run
    (selected : Bool) (witness : BitString)
    (crossed remaining : Nat) :
    preservingUnaryReadMachine.run (remaining + 1)
      (cleanupScanConfig selected witness crossed remaining) =
      haltedConfig selected witness (crossed + remaining + 1) := by
  induction remaining generalizing crossed with
  | zero =>
      cases selected <;>
        simp [cleanupScanConfig, haltedConfig, preservingUnaryReadMachine,
          TM.run, TM.step, Tape.write, Tape.move,
          List.replicate_succ, List.append_assoc]
  | succ remaining ih =>
      cases selected <;>
        simp only [cleanupScanConfig, preservingUnaryReadMachine, TM.run]
      · have hstep :
            preservingUnaryReadMachine.step
              (cleanupScanConfig false witness crossed (remaining + 1)) =
            cleanupScanConfig false witness (crossed + 1) remaining := by
          cases remaining <;>
            simp [cleanupScanConfig, preservingUnaryReadMachine,
              TM.step, Tape.write, Tape.move,
              List.replicate_succ, List.append_assoc]
        have hrun :
            preservingUnaryReadMachine.run (remaining + 2)
              (cleanupScanConfig false witness crossed (remaining + 1)) =
            preservingUnaryReadMachine.run (remaining + 1)
              (cleanupScanConfig false witness (crossed + 1) remaining) := by
          rw [show remaining + 2 = (remaining + 1) + 1 by omega]
          rw [TM.run]
          simp only [cleanupScanConfig_state_false,
            preserving_not_halt_cleanupFalse, Bool.false_eq_true, if_false]
          rw [hstep]
        have h := ih (crossed := crossed + 1)
        calc
          preservingUnaryReadMachine.run (Nat.succ remaining + 1)
              (cleanupScanConfig false witness crossed (Nat.succ remaining))
              =
            preservingUnaryReadMachine.run (remaining + 2)
              (cleanupScanConfig false witness crossed (remaining + 1)) := by
                congr 2 <;> omega
          _ =
            preservingUnaryReadMachine.run (remaining + 1)
              (cleanupScanConfig false witness (crossed + 1) remaining) := hrun
          _ = haltedConfig false witness ((crossed + 1) + remaining + 1) := h
          _ = haltedConfig false witness (crossed + Nat.succ remaining + 1) := by
                congr 1
                omega
      · have hstep :
            preservingUnaryReadMachine.step
              (cleanupScanConfig true witness crossed (remaining + 1)) =
            cleanupScanConfig true witness (crossed + 1) remaining := by
          cases remaining <;>
            simp [cleanupScanConfig, preservingUnaryReadMachine,
              TM.step, Tape.write, Tape.move,
              List.replicate_succ, List.append_assoc]
        have hrun :
            preservingUnaryReadMachine.run (remaining + 2)
              (cleanupScanConfig true witness crossed (remaining + 1)) =
            preservingUnaryReadMachine.run (remaining + 1)
              (cleanupScanConfig true witness (crossed + 1) remaining) := by
          rw [show remaining + 2 = (remaining + 1) + 1 by omega]
          rw [TM.run]
          simp only [cleanupScanConfig_state_true,
            preserving_not_halt_cleanupTrue, Bool.false_eq_true, if_false]
          rw [hstep]
        have h := ih (crossed := crossed + 1)
        calc
          preservingUnaryReadMachine.run (Nat.succ remaining + 1)
              (cleanupScanConfig true witness crossed (Nat.succ remaining))
              =
            preservingUnaryReadMachine.run (remaining + 2)
              (cleanupScanConfig true witness crossed (remaining + 1)) := by
                congr 2 <;> omega
          _ =
            preservingUnaryReadMachine.run (remaining + 1)
              (cleanupScanConfig true witness (crossed + 1) remaining) := hrun
          _ = haltedConfig true witness ((crossed + 1) + remaining + 1) := h
          _ = haltedConfig true witness (crossed + Nat.succ remaining + 1) := by
                congr 1
                omega

/-- Full physical rewind and cleanup for every nonempty traversed prefix. -/
theorem preservingRead_rewind_cleanup
    (a : Bool) (rest : BitString) (b : Bool) (suffix : BitString) :
    preservingUnaryReadMachine.run (4 * (a :: rest).length + 2)
      (selectedConfig (a :: rest) b suffix) =
      haltedConfig b ((a :: rest) ++ b :: suffix) ((a :: rest).length + 2) := by
  let pref : BitString := a :: rest
  have hp : pref ≠ [] := by simp [pref]
  obtain ⟨x, xs, hrev, hentry⟩ :=
    selected_to_rewind_active pref b suffix hp
  have hlen : (x :: xs).length = pref.length := by
    rw [← hrev, List.length_reverse]
  have hpos : 0 < pref.length := by simp [pref]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hrew :
      preservingUnaryReadMachine.run (3 * pref.length)
        (rewindActiveConfig b x xs (b :: suffix) pref.length) =
      rewindDoneConfig b (pref ++ b :: suffix) k := by
    have h :=
      rewind_all_active b x xs (b :: suffix) k
    have hblanks : pref.length = k + 1 := hk
    have hrevrev : (x :: xs).reverse = pref := by
      rw [← hrev, List.reverse_reverse]
    simpa [hlen, hblanks, hrevrev, List.append_assoc] using h
  have hclean :
      preservingUnaryReadMachine.run (k + 2)
        (rewindDoneConfig b (pref ++ b :: suffix) k) =
      haltedConfig b (pref ++ b :: suffix) (pref.length + 2) := by
    rw [show k + 2 = 1 + (k + 1) by omega]
    rw [run_add, rewind_done_enter_cleanup]
    have h := cleanup_scan_run b (pref ++ b :: suffix) 2 k
    have hcount : 2 + k + 1 = pref.length + 2 := by omega
    rw [← hcount]
    exact h
  have hfuel :
      4 * pref.length + 2 = 1 + (3 * pref.length + (k + 2)) := by
    omega
  change preservingUnaryReadMachine.run (4 * pref.length + 2)
      (selectedConfig pref b suffix) =
    haltedConfig b (pref ++ b :: suffix) (pref.length + 2)
  rw [hfuel]
  calc
    preservingUnaryReadMachine.run
        (1 + (3 * pref.length + (k + 2)))
        (selectedConfig pref b suffix)
        =
      preservingUnaryReadMachine.run
        (3 * pref.length + (k + 2))
        (preservingUnaryReadMachine.run 1
          (selectedConfig pref b suffix)) := by
            rw [run_add]
    _ =
      preservingUnaryReadMachine.run
        (3 * pref.length + (k + 2))
        (rewindActiveConfig b x xs (b :: suffix) pref.length) := by
          rw [hentry]
    _ =
      preservingUnaryReadMachine.run (k + 2)
        (preservingUnaryReadMachine.run (3 * pref.length)
          (rewindActiveConfig b x xs (b :: suffix) pref.length)) := by
          rw [run_add]
    _ =
      preservingUnaryReadMachine.run (k + 2)
        (rewindDoneConfig b (pref ++ b :: suffix) k) := by
          rw [hrew]
    _ = haltedConfig b (pref ++ b :: suffix) (pref.length + 2) := hclean

#print axioms MCore.Real.P01PreservingUnaryRewind.preservingRead_rewind_cleanup

end P01PreservingUnaryRewind
end Real
end MCore
