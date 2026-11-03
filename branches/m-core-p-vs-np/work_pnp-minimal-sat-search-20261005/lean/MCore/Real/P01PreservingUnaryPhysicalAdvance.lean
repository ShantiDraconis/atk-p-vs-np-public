import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore.Real.P01PreservingUnaryPhysicalAdvance

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

/-- Exact seekBlanks state: `remaining` erased blanks are still to the left,
while `passed` erased blanks have already been crossed and sit to the right.
The current head is itself a blank. -/
def seekBlanksConfig
    (remaining passed : Nat)
    (traversed : BitString)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left :=
          List.replicate remaining none ++
            traversed.map some ++ none :: (b :: tail).map some
        head := none
        right :=
          List.replicate (passed + 1) none ++
            (encodeNat n).map some } }

@[simp] theorem seekBlanksConfig_state
    (remaining passed : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    (seekBlanksConfig remaining passed traversed b tail n).state =
      .seekBlanks := rfl

/-- One physical left move transfers one erased blank from remaining to passed. -/
theorem seekBlanks_step_succ
    (remaining passed : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.step
      (seekBlanksConfig (remaining + 1) passed traversed b tail n) =
      seekBlanksConfig remaining (passed + 1) traversed b tail n := by
  simp [seekBlanksConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Scan all remaining erased blanks. -/
theorem seekBlanks_run
    (remaining passed : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run remaining
      (seekBlanksConfig remaining passed traversed b tail n) =
      seekBlanksConfig 0 (passed + remaining) traversed b tail n := by
  induction remaining generalizing passed with
  | zero =>
      rfl
  | succ remaining ih =>
      calc
        preservingUnaryReadMachine.run (Nat.succ remaining)
            (seekBlanksConfig (Nat.succ remaining) passed traversed b tail n) =
          preservingUnaryReadMachine.run remaining
            (preservingUnaryReadMachine.step
              (seekBlanksConfig (remaining + 1) passed traversed b tail n)) := by
                simp [TM.run, preservingUnaryReadMachine, Nat.succ_eq_add_one]
        _ = preservingUnaryReadMachine.run remaining
            (seekBlanksConfig remaining (passed + 1) traversed b tail n) := by
              rw [seekBlanks_step_succ]
        _ = seekBlanksConfig 0 ((passed + 1) + remaining) traversed b tail n :=
              ih (passed := passed + 1)
        _ = seekBlanksConfig 0 (passed + Nat.succ remaining) traversed b tail n := by
              have hNat :
                  ((passed + 1) + remaining) =
                    (passed + Nat.succ remaining) := by
                omega
              exact congrArg
                (fun k => seekBlanksConfig 0 k traversed b tail n) hNat

/-- With no erased blank left, the next step sees the first traversed bit. -/
def seekBitsEntryConfig
    (x : Bool) (xs : BitString)
    (passed : Nat)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left := xs.map some ++ none :: (b :: tail).map some
        head := some x
        right :=
          List.replicate (passed + 1) none ++ (encodeNat n).map some } }

theorem seekBlanks_zero_step_to_bits
    (x : Bool) (xs : BitString) (passed : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (seekBlanksConfig 0 passed (x :: xs) b tail n) =
      seekBitsEntryConfig x xs (passed + 1) b tail n := by
  simp [seekBlanksConfig, seekBitsEntryConfig, preservingUnaryReadMachine,
    TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
    List.append_assoc, Nat.add_assoc]

/-- seekBits state after one traversed bit has been crossed. -/
def seekBitsConfig
    (remaining : BitString)
    (passedRev : BitString)
    (blankPad : Nat)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .seekBits
        tape :=
          { left := (b :: tail).map some
            head := none
            right :=
              passedRev.map some ++
                List.replicate blankPad none ++ (encodeNat n).map some } }
  | y :: ys =>
      { state := .seekBits
        tape :=
          { left := ys.map some ++ none :: (b :: tail).map some
            head := some y
            right :=
              passedRev.map some ++
                List.replicate blankPad none ++ (encodeNat n).map some } }

theorem seekBits_entry_step
    (x : Bool) (xs : BitString) (passed : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (seekBitsEntryConfig x xs passed b tail n) =
      seekBitsConfig xs [x] (passed + 1) b tail n := by
  cases xs <;>
    simp [seekBitsEntryConfig, seekBitsConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]


@[simp] theorem seekBitsConfig_state
    (remaining passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    (seekBitsConfig remaining passedRev blankPad b tail n).state = .seekBits := by
  cases remaining <;> rfl

/-- One traversed witness bit is crossed by seekBits. -/
theorem seekBits_step_cons
    (y : Bool) (ys passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.step
      (seekBitsConfig (y :: ys) passedRev blankPad b tail n) =
      seekBitsConfig ys (y :: passedRev) blankPad b tail n := by
  cases ys <;>
    simp [seekBitsConfig, preservingUnaryReadMachine, TM.step,
      Tape.write, Tape.move, List.append_assoc]

/-- Scan all traversed witness bits until the marker blank is under the head. -/
theorem seekBits_run
    (remaining passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run remaining.length
      (seekBitsConfig remaining passedRev blankPad b tail n) =
      seekBitsConfig [] (remaining.reverse ++ passedRev) blankPad b tail n := by
  induction remaining generalizing passedRev with
  | nil =>
      rfl
  | cons y ys ih =>
      calc
        preservingUnaryReadMachine.run (y :: ys).length
            (seekBitsConfig (y :: ys) passedRev blankPad b tail n) =
          preservingUnaryReadMachine.run ys.length
            (preservingUnaryReadMachine.step
              (seekBitsConfig (y :: ys) passedRev blankPad b tail n)) := by
                simp [TM.run, preservingUnaryReadMachine]
        _ = preservingUnaryReadMachine.run ys.length
            (seekBitsConfig ys (y :: passedRev) blankPad b tail n) := by
              rw [seekBits_step_cons]
        _ = seekBitsConfig [] (ys.reverse ++ (y :: passedRev)) blankPad b tail n :=
              ih (passedRev := y :: passedRev)
        _ = seekBitsConfig [] ((y :: ys).reverse ++ passedRev) blankPad b tail n := by
              simp [List.reverse_cons, List.append_assoc]

/-- At the marker blank, one physical step enters shiftRead and moves onto the
next witness bit that will be shifted across the marker. -/
def shiftReadConfig
    (passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .shiftRead
    tape :=
      { left := tail.map some
        head := some b
        right := none :: passedRev.map some ++
          List.replicate blankPad none ++ (encodeNat n).map some } }

theorem seekBits_marker_to_shiftRead
    (passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (seekBitsConfig [] passedRev blankPad b tail n) =
      shiftReadConfig passedRev blankPad b tail n := by
  simp [seekBitsConfig, shiftReadConfig, preservingUnaryReadMachine,
    TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]


/-- Configuration immediately after shiftRead has erased the selected witness
cell and moved right onto the marker blank. -/
def carryConfig
    (selected : Bool)
    (passedRev : BitString) (blankPad : Nat)
    (tail : BitString) (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := if selected then .carryTrue else .carryFalse
    tape :=
      { left := none :: tail.map some
        head := none
        right := passedRev.map some ++
          List.replicate blankPad none ++ (encodeNat n).map some } }

/-- shiftRead performs the physical erase-and-carry step. -/
theorem shiftRead_to_carry
    (passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (shiftReadConfig passedRev blankPad b tail n) =
      carryConfig b passedRev blankPad tail n := by
  cases b <;>
    simp [shiftReadConfig, carryConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

/-- After carrying the selected bit back onto the marker cell, control enters
returnFromMarker and moves left to the new marker blank. -/
def returnFromMarkerConfig
    (selected : Bool)
    (passedRev : BitString) (blankPad : Nat)
    (tail : BitString) (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .returnFromMarker
    tape :=
      { left := tail.map some
        head := none
        right := some selected :: passedRev.map some ++
          List.replicate blankPad none ++ (encodeNat n).map some } }

theorem carry_to_returnFromMarker
    (selected : Bool)
    (passedRev : BitString) (blankPad : Nat)
    (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (carryConfig selected passedRev blankPad tail n) =
      returnFromMarkerConfig selected passedRev blankPad tail n := by
  cases selected <;>
    simp [carryConfig, returnFromMarkerConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

/-- returnBits scans right across the restored selected bit and the traversed
prefix.  `leftAcc` is the exact physical left stack accumulated so far. -/
def returnBitsConfig
    (remaining : BitString)
    (leftAcc : List (Option Bool))
    (blankPad : Nat) (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .returnBits
        tape :=
          { left := leftAcc
            head := none
            right := List.replicate (blankPad - 1) none ++ (encodeNat n).map some } }
  | x :: xs =>
      { state := .returnBits
        tape :=
          { left := leftAcc
            head := some x
            right := xs.map some ++
              List.replicate blankPad none ++ (encodeNat n).map some } }

/-- returnFromMarker crosses the marker blank.  The selected bit becomes the
first returnBits head and the moved marker blank is now in the left stack. -/
theorem returnFromMarker_to_returnBits
    (selected : Bool)
    (passedRev : BitString) (blankPad : Nat)
    (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (returnFromMarkerConfig selected passedRev blankPad tail n) =
      returnBitsConfig (selected :: passedRev) (none :: tail.map some)
        blankPad n := by
  simp [returnFromMarkerConfig, returnBitsConfig,
    preservingUnaryReadMachine, TM.run, TM.step,
    Tape.write, Tape.move, List.append_assoc]

@[simp] theorem returnBitsConfig_state
    (remaining : BitString) (leftAcc : List (Option Bool))
    (blankPad : Nat) (n : Nat) :
    (returnBitsConfig remaining leftAcc blankPad n).state = .returnBits := by
  cases remaining <;> rfl

/-- One physical returnBits step preserves the current bit and moves right. -/
theorem returnBits_step_cons
    (x : Bool) (xs : BitString) (leftAcc : List (Option Bool))
    (blankPad : Nat) (n : Nat) (hpad : 0 < blankPad) :
    preservingUnaryReadMachine.step
      (returnBitsConfig (x :: xs) leftAcc blankPad n) =
      returnBitsConfig xs (some x :: leftAcc) blankPad n := by
  cases blankPad with
  | zero => omega
  | succ k =>
      cases xs <;>
        simp [returnBitsConfig, preservingUnaryReadMachine, TM.step,
          Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

/-- Exact physical scan of all restored bits until the blank separator is under
the head.  The scanned sequence is reversed into the physical left stack. -/
theorem returnBits_run
    (remaining : BitString) (leftAcc : List (Option Bool))
    (blankPad : Nat) (n : Nat) (hpad : 0 < blankPad) :
    preservingUnaryReadMachine.run remaining.length
      (returnBitsConfig remaining leftAcc blankPad n) =
      returnBitsConfig [] (remaining.reverse.map some ++ leftAcc) blankPad n := by
  induction remaining generalizing leftAcc with
  | nil =>
      rfl
  | cons x xs ih =>
      calc
        preservingUnaryReadMachine.run (x :: xs).length
            (returnBitsConfig (x :: xs) leftAcc blankPad n) =
          preservingUnaryReadMachine.run xs.length
            (preservingUnaryReadMachine.step
              (returnBitsConfig (x :: xs) leftAcc blankPad n)) := by
                simp [TM.run, preservingUnaryReadMachine]
        _ = preservingUnaryReadMachine.run xs.length
            (returnBitsConfig xs (some x :: leftAcc) blankPad n) := by
              rw [returnBits_step_cons x xs leftAcc blankPad n hpad]
        _ = returnBitsConfig []
            (xs.reverse.map some ++ (some x :: leftAcc)) blankPad n :=
              ih (leftAcc := some x :: leftAcc)
        _ = returnBitsConfig []
            ((x :: xs).reverse.map some ++ leftAcc) blankPad n := by
              simp [List.reverse_cons, List.map_append, List.append_assoc]


/-- returnBlanks configuration after returnBits has crossed the separator.
When `remaining` is zero, the head is the next unary symbol. -/
def returnBlanksConfig
    (remaining : Nat)
    (leftAcc : List (Option Bool))
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | 0 =>
      match encodeNat n with
      | [] =>
          { state := .reject
            tape := { left := leftAcc, head := none, right := [] } }
      | bit :: rest =>
          { state := .returnBlanks
            tape :=
              { left := leftAcc
                head := some bit
                right := rest.map some } }
  | k + 1 =>
      { state := .returnBlanks
        tape :=
          { left := leftAcc
            head := none
            right := List.replicate k none ++ (encodeNat n).map some } }

@[simp] theorem returnBlanksConfig_state
    (remaining : Nat) (leftAcc : List (Option Bool)) (n : Nat) :
    (returnBlanksConfig remaining leftAcc n).state =
      if remaining = 0 ∧ encodeNat n = [] then .reject else .returnBlanks := by
  cases remaining with
  | zero =>
      cases h : encodeNat n <;> simp [returnBlanksConfig, h]
  | succ k =>
      simp [returnBlanksConfig]

/-- Crossing the separator blank enters returnBlanks. -/
theorem returnBits_to_returnBlanks
    (leftAcc : List (Option Bool)) (blankPad : Nat) (n : Nat)
    (hpad : 0 < blankPad) :
    preservingUnaryReadMachine.run 1
      (returnBitsConfig [] leftAcc blankPad n) =
      returnBlanksConfig (blankPad - 1) (none :: leftAcc) n := by
  cases blankPad with
  | zero => omega
  | succ k =>
      cases k with
      | zero =>
          have hnonempty : encodeNat n ≠ [] := by
            cases n <;> simp [encodeNat]
          cases h : encodeNat n with
          | nil =>
              exact (hnonempty h).elim
          | cons bit rest =>
              simp [returnBitsConfig, returnBlanksConfig, preservingUnaryReadMachine,
                TM.run, TM.step, Tape.write, Tape.move, h]
      | succ k =>
          simp [returnBitsConfig, returnBlanksConfig, preservingUnaryReadMachine,
            TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
            List.append_assoc]

/-- One erased blank is crossed by returnBlanks. -/
theorem returnBlanks_step_succ
    (k : Nat) (leftAcc : List (Option Bool)) (n : Nat) :
    preservingUnaryReadMachine.step
      (returnBlanksConfig (k + 1) leftAcc n) =
      returnBlanksConfig k (none :: leftAcc) n := by
  cases k with
  | zero =>
      cases n <;>
        simp [returnBlanksConfig, preservingUnaryReadMachine, encodeNat,
          TM.step, Tape.write, Tape.move]
  | succ k =>
      simp [returnBlanksConfig, preservingUnaryReadMachine, TM.step,
        Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

/-- Prepending one blank after a replicated blank block is the same as
prepending it before the block. -/
theorem replicate_none_append_cons
    (k : Nat) (leftAcc : List (Option Bool)) :
    List.replicate k none ++ none :: leftAcc =
      none :: (List.replicate k none ++ leftAcc) := by
  induction k generalizing leftAcc with
  | zero => rfl
  | succ k ih =>
      simp [List.replicate_succ, ih, List.append_assoc]

/-- Scan all erased unary blanks and land on the next unary symbol. -/
theorem returnBlanks_run
    (remaining : Nat) (leftAcc : List (Option Bool)) (n : Nat) :
    preservingUnaryReadMachine.run remaining
      (returnBlanksConfig remaining leftAcc n) =
      returnBlanksConfig 0 (List.replicate remaining none ++ leftAcc) n := by
  induction remaining generalizing leftAcc with
  | zero =>
      rfl
  | succ k ih =>
      calc
        preservingUnaryReadMachine.run (Nat.succ k)
            (returnBlanksConfig (Nat.succ k) leftAcc n) =
          preservingUnaryReadMachine.run k
            (preservingUnaryReadMachine.step
              (returnBlanksConfig (k + 1) leftAcc n)) := by
                simp [TM.run, returnBlanksConfig, preservingUnaryReadMachine,
                  Nat.succ_eq_add_one]
        _ = preservingUnaryReadMachine.run k
            (returnBlanksConfig k (none :: leftAcc) n) := by
              rw [returnBlanks_step_succ]
        _ = returnBlanksConfig 0
            (List.replicate k none ++ (none :: leftAcc)) n :=
              ih (leftAcc := none :: leftAcc)
        _ = returnBlanksConfig 0
            (List.replicate (Nat.succ k) none ++ leftAcc) n := by
              simpa [List.replicate_succ] using
                congrArg (fun z => returnBlanksConfig 0 z n)
                  (replicate_none_append_cons k leftAcc)

/-- Once the blank region is exhausted, returnBlanks sees the next encoded
unary symbol and returns to indexSome without moving the head. -/
theorem returnBlanks_zero_to_indexSome
    (leftAcc : List (Option Bool)) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (returnBlanksConfig 0 leftAcc n) =
      { state := .indexSome
        tape :=
          { left := leftAcc
            head := (encodeNat n).head?
            right := (encodeNat n).tail.map some } } := by
  cases n <;>
    simp [returnBlanksConfig, preservingUnaryReadMachine, encodeNat,
      TM.run, TM.step, Tape.write, Tape.move]



/-- Final nonzero read: scan the erased unary-true blanks leftward. -/
def finalSeekBlanksConfig
    (remaining passed : Nat)
    (traversed : BitString)
    (selected : Bool) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .finalSeekBlanks
    tape :=
      { left :=
          List.replicate remaining none ++
            traversed.map some ++ none :: (selected :: tail).map some
        head := none
        right := List.replicate passed none ++ [some false] } }

@[simp] theorem finalSeekBlanksConfig_state
    (remaining passed : Nat) (traversed : BitString)
    (selected : Bool) (tail : BitString) :
    (finalSeekBlanksConfig remaining passed traversed selected tail).state =
      .finalSeekBlanks := rfl

theorem finalSeekBlanks_step_succ
    (remaining passed : Nat) (traversed : BitString)
    (selected : Bool) (tail : BitString) :
    preservingUnaryReadMachine.step
      (finalSeekBlanksConfig (remaining + 1) passed traversed selected tail) =
      finalSeekBlanksConfig remaining (passed + 1) traversed selected tail := by
  simp [finalSeekBlanksConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem finalSeekBlanks_run
    (remaining passed : Nat) (traversed : BitString)
    (selected : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run remaining
      (finalSeekBlanksConfig remaining passed traversed selected tail) =
      finalSeekBlanksConfig 0 (passed + remaining) traversed selected tail := by
  induction remaining generalizing passed with
  | zero => rfl
  | succ remaining ih =>
      calc
        preservingUnaryReadMachine.run (Nat.succ remaining)
            (finalSeekBlanksConfig (Nat.succ remaining) passed traversed selected tail) =
          preservingUnaryReadMachine.run remaining
            (preservingUnaryReadMachine.step
              (finalSeekBlanksConfig (remaining + 1) passed traversed selected tail)) := by
                simp [TM.run, preservingUnaryReadMachine, Nat.succ_eq_add_one]
        _ = preservingUnaryReadMachine.run remaining
            (finalSeekBlanksConfig remaining (passed + 1) traversed selected tail) := by
              rw [finalSeekBlanks_step_succ]
        _ = finalSeekBlanksConfig 0 ((passed + 1) + remaining)
            traversed selected tail := ih (passed := passed + 1)
        _ = finalSeekBlanksConfig 0 (passed + Nat.succ remaining)
            traversed selected tail := by
              have h : (passed + 1) + remaining = passed + Nat.succ remaining := by omega
              exact congrArg
                (fun k => finalSeekBlanksConfig 0 k traversed selected tail) h

/-- Entry to finalSeekBits after all erased blanks have been crossed. -/
def finalSeekBitsEntryConfig
    (x : Bool) (xs : BitString) (passed : Nat)
    (selected : Bool) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .finalSeekBlanks
    tape :=
      { left := xs.map some ++ none :: (selected :: tail).map some
        head := some x
        right := List.replicate (passed + 1) none ++ [some false] } }

theorem finalSeekBlanks_zero_step_to_bits
    (x : Bool) (xs : BitString) (passed : Nat)
    (selected : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run 1
      (finalSeekBlanksConfig 0 passed (x :: xs) selected tail) =
      finalSeekBitsEntryConfig x xs passed selected tail := by
  simp [finalSeekBlanksConfig, finalSeekBitsEntryConfig,
    preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move,
    List.replicate_succ, List.append_assoc, Nat.add_assoc]

def finalSeekBitsConfig
    (remaining passedRev : BitString) (blankPad : Nat)
    (selected : Bool) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .finalSeekBits
        tape :=
          { left := (selected :: tail).map some
            head := none
            right := passedRev.map some ++
              List.replicate blankPad none ++ [some false] } }
  | y :: ys =>
      { state := .finalSeekBits
        tape :=
          { left := ys.map some ++ none :: (selected :: tail).map some
            head := some y
            right := passedRev.map some ++
              List.replicate blankPad none ++ [some false] } }

@[simp] theorem finalSeekBitsConfig_state
    (remaining passedRev : BitString) (blankPad : Nat)
    (selected : Bool) (tail : BitString) :
    (finalSeekBitsConfig remaining passedRev blankPad selected tail).state =
      .finalSeekBits := by
  cases remaining <;> rfl

theorem finalSeekBits_entry_step
    (x : Bool) (xs : BitString) (passed : Nat)
    (selected : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run 1
      (finalSeekBitsEntryConfig x xs passed selected tail) =
      finalSeekBitsConfig xs [x] (passed + 1) selected tail := by
  cases xs <;>
    simp [finalSeekBitsEntryConfig, finalSeekBitsConfig,
      preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem finalSeekBits_step_cons
    (y : Bool) (ys passedRev : BitString) (blankPad : Nat)
    (selected : Bool) (tail : BitString) :
    preservingUnaryReadMachine.step
      (finalSeekBitsConfig (y :: ys) passedRev blankPad selected tail) =
      finalSeekBitsConfig ys (y :: passedRev) blankPad selected tail := by
  cases ys <;>
    simp [finalSeekBitsConfig, preservingUnaryReadMachine, TM.step,
      Tape.write, Tape.move, List.append_assoc]

theorem finalSeekBits_run
    (remaining passedRev : BitString) (blankPad : Nat)
    (selected : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run remaining.length
      (finalSeekBitsConfig remaining passedRev blankPad selected tail) =
      finalSeekBitsConfig [] (remaining.reverse ++ passedRev)
        blankPad selected tail := by
  induction remaining generalizing passedRev with
  | nil => rfl
  | cons y ys ih =>
      calc
        preservingUnaryReadMachine.run (y :: ys).length
            (finalSeekBitsConfig (y :: ys) passedRev blankPad selected tail) =
          preservingUnaryReadMachine.run ys.length
            (preservingUnaryReadMachine.step
              (finalSeekBitsConfig (y :: ys) passedRev blankPad selected tail)) := by
                simp [TM.run, preservingUnaryReadMachine]
        _ = preservingUnaryReadMachine.run ys.length
            (finalSeekBitsConfig ys (y :: passedRev) blankPad selected tail) := by
              rw [finalSeekBits_step_cons]
        _ = finalSeekBitsConfig [] (ys.reverse ++ (y :: passedRev))
            blankPad selected tail := ih (passedRev := y :: passedRev)
        _ = finalSeekBitsConfig [] ((y :: ys).reverse ++ passedRev)
            blankPad selected tail := by
              simp [List.reverse_cons, List.append_assoc]

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.finalSeekBlanks_step_succ
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.finalSeekBlanks_run
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.finalSeekBlanks_zero_step_to_bits
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.finalSeekBits_entry_step
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.finalSeekBits_step_cons
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.finalSeekBits_run

/-- Universal physical marker cycle.  A nonempty traversed prefix of length L
costs exactly 4*L+8 steps and extends the canonical prefix by one witness bit. -/
theorem indexSome_run_advance
    (traversed : BitString) (b : Bool) (tail : BitString) (n : Nat)
    (htrav : traversed ≠ []) :
    preservingUnaryReadMachine.run (4 * traversed.length + 8)
      (indexSomeConfig traversed (b :: tail) (n + 1)) =
      indexSomeConfig (traversed ++ [b]) tail n := by
  cases traversed with
  | nil =>
      exact (htrav rfl).elim
  | cons x xs =>
      let L := xs.length + 1
      have hL : (x :: xs).length = L := by
        simp [L]
      have hpad : 0 < L + 1 := by
        omega
      have hentry :
          preservingUnaryReadMachine.run 1
            (indexSomeConfig (x :: xs) (b :: tail) (n + 1)) =
          seekBlanksConfig xs.length 0 (x :: xs) b tail n := by
        simp [indexSomeConfig, seekBlanksConfig, preservingUnaryReadMachine,
          encodeNat, TM.run, TM.step, Tape.write, Tape.move,
          List.replicate_succ, List.append_assoc]
      rw [hL]
      have hcost :
          4 * L + 8 =
            1 + (xs.length + (1 + (1 + (xs.length +
              (1 + (1 + (1 + (1 + ((L + 1) + (1 + (L + 1))))))))))) := by
        simp [L]
        omega
      rw [hcost]
      rw [run_add, hentry]
      rw [run_add, seekBlanks_run]
      rw [run_add, seekBlanks_zero_step_to_bits]
      rw [run_add, seekBits_entry_step]
      rw [run_add, seekBits_run]
      rw [run_add, seekBits_marker_to_shiftRead]
      rw [run_add, shiftRead_to_carry]
      rw [run_add, carry_to_returnFromMarker]
      rw [run_add, returnFromMarker_to_returnBits]
      simp only [L, Nat.zero_add] at *
      change preservingUnaryReadMachine.run
        ((xs.length + 1 + 1) + (1 + (xs.length + 1 + 1)))
        (returnBitsConfig (b :: (xs.reverse ++ [x]))
          (none :: tail.map some) (xs.length + 1 + 1) n) =
        indexSomeConfig ((x :: xs) ++ [b]) tail n
      have hrem :
          (b :: (xs.reverse ++ [x])).length = L + 1 := by
        simp [L]
      have hbits :
          preservingUnaryReadMachine.run (L + 1)
            (returnBitsConfig (b :: (xs.reverse ++ [x]))
              (none :: tail.map some) (L + 1) n) =
          returnBitsConfig []
            ((b :: (xs.reverse ++ [x])).reverse.map some ++
              (none :: tail.map some)) (L + 1) n := by
        simpa [hrem] using
          (returnBits_run
            (b :: (xs.reverse ++ [x]))
            (none :: tail.map some) (L + 1) n hpad)
      rw [run_add, hbits]
      rw [run_add, returnBits_to_returnBlanks _ _ _ hpad]
      have hsub : (L + 1) - 1 = L := by omega
      rw [hsub]
      rw [run_add, returnBlanks_run]
      rw [returnBlanks_zero_to_indexSome]
      cases n <;>
        simp [L, indexSomeConfig, List.map_append, List.reverse_cons,
          List.append_assoc, List.replicate_succ, encodeNat,
          replicate_none_append_cons]

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.indexSome_run_advance

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.returnBits_to_returnBlanks
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.returnBlanks_step_succ
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.returnBlanks_run
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.returnBlanks_zero_to_indexSome

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.returnFromMarker_to_returnBits
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.returnBits_step_cons
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.returnBits_run

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.shiftRead_to_carry
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.carry_to_returnFromMarker
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.returnFromMarker_to_returnBits

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBits_step_cons
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBits_run
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBits_marker_to_shiftRead

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_step_succ
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_run
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_zero_step_to_bits
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBits_entry_step

end MCore.Real.P01PreservingUnaryPhysicalAdvance
