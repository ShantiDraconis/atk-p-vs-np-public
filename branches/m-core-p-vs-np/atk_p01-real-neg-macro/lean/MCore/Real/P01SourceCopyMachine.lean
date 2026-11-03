import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace P01SourceCopyMachine

open CanonicalFinalProof

/-
Deterministic source copier over the existing Option Bool alphabet.

Layout during the loop:
  original-prefix [blanked current] original-suffix blank copy

The temporary blanked current cell is the second blank encountered while
returning from the right. The bit value is stored only in finite control.
At completion:
  original blank copy
and the head is moved to the first cell of copy (or blank for empty input).
-/

abbrev CopyState := Fin 11

def nextCell : CopyState := 0
def seekDelimiterFalse : CopyState := 1
def seekDelimiterTrue : CopyState := 2
def seekCopyEndFalse : CopyState := 3
def seekCopyEndTrue : CopyState := 4
def returnToDelimiterFalse : CopyState := 5
def returnToDelimiterTrue : CopyState := 6
def returnToHoleFalse : CopyState := 7
def returnToHoleTrue : CopyState := 8
def enterCopy : CopyState := 9
def copyHalt : CopyState := 10

def sourceCopyMachine : TM CopyState (Option Bool) :=
  { initial := nextCell
    blank := none
    transition := fun q symbol =>
      if q = nextCell then
        match symbol with
        | some false => (seekDelimiterFalse, none, .right)
        | some true  => (seekDelimiterTrue, none, .right)
        | none       => (enterCopy, none, .right)
      else if q = seekDelimiterFalse then
        match symbol with
        | some b => (seekDelimiterFalse, some b, .right)
        | none   => (seekCopyEndFalse, none, .right)
      else if q = seekDelimiterTrue then
        match symbol with
        | some b => (seekDelimiterTrue, some b, .right)
        | none   => (seekCopyEndTrue, none, .right)
      else if q = seekCopyEndFalse then
        match symbol with
        | some b => (seekCopyEndFalse, some b, .right)
        | none   => (returnToDelimiterFalse, some false, .left)
      else if q = seekCopyEndTrue then
        match symbol with
        | some b => (seekCopyEndTrue, some b, .right)
        | none   => (returnToDelimiterTrue, some true, .left)
      else if q = returnToDelimiterFalse then
        match symbol with
        | some b => (returnToDelimiterFalse, some b, .left)
        | none   => (returnToHoleFalse, none, .left)
      else if q = returnToDelimiterTrue then
        match symbol with
        | some b => (returnToDelimiterTrue, some b, .left)
        | none   => (returnToHoleTrue, none, .left)
      else if q = returnToHoleFalse then
        match symbol with
        | some b => (returnToHoleFalse, some b, .left)
        | none   => (nextCell, some false, .right)
      else if q = returnToHoleTrue then
        match symbol with
        | some b => (returnToHoleTrue, some b, .left)
        | none   => (nextCell, some true, .right)
      else if q = enterCopy then
        (copyHalt, symbol, .stay)
      else
        (copyHalt, symbol, .stay)
    halting := fun q => q == copyHalt }

@[simp] theorem sourceCopyMachine_blank :
    sourceCopyMachine.blank = none := rfl

@[simp] theorem sourceCopyMachine_initial :
    sourceCopyMachine.initial = nextCell := rfl

@[simp] theorem sourceCopyMachine_halt :
    sourceCopyMachine.halting copyHalt = true := by decide

@[simp] theorem sourceCopyMachine_next_not_halt :
    sourceCopyMachine.halting nextCell = false := by decide

/-- Conservative cubic bound for repeated whole-tape shuttles. -/
def sourceCopyTimeBound : TimeBound :=
  fun n => 16 * (n + 1) ^ 3

theorem sourceCopyTimeBound_poly :
    PolynomialTimeBound sourceCopyTimeBound := by
  exact ⟨16, 3, fun n => Nat.le_refl _⟩

/-- Empty source reaches the copy entry and then halts. -/
theorem sourceCopy_empty :
    sourceCopyMachine.run 2
      (initialTMConfig sourceCopyMachine []) =
      { state := copyHalt,
        tape := { left := [none], head := none, right := [] } } := by
  simp [sourceCopyMachine, nextCell, seekDelimiterFalse, seekDelimiterTrue,
    seekCopyEndFalse, seekCopyEndTrue, returnToDelimiterFalse,
    returnToDelimiterTrue, returnToHoleFalse, returnToHoleTrue,
    enterCopy, copyHalt, TM.run, TM.step, initialTMConfig, inputTape,
    Tape.write, Tape.move]

/-- The first step stores the current source bit in finite control and leaves
a unique temporary blank hole at its original position. -/
theorem sourceCopy_first_false
    (bs : BitString) :
    sourceCopyMachine.step
      (initialTMConfig sourceCopyMachine (false :: bs)) =
      { state := seekDelimiterFalse,
        tape := Tape.move none .right
          ((inputTape (false :: bs)).write none) } := by
  cases bs <;>
    simp [sourceCopyMachine, nextCell, seekDelimiterFalse, seekDelimiterTrue,
      enterCopy, initialTMConfig, inputTape, TM.step, Tape.write, Tape.move]

theorem sourceCopy_first_true
    (bs : BitString) :
    sourceCopyMachine.step
      (initialTMConfig sourceCopyMachine (true :: bs)) =
      { state := seekDelimiterTrue,
        tape := Tape.move none .right
          ((inputTape (true :: bs)).write none) } := by
  cases bs <;>
    simp [sourceCopyMachine, nextCell, seekDelimiterFalse, seekDelimiterTrue,
      enterCopy, initialTMConfig, inputTape, TM.step, Tape.write, Tape.move]

#print axioms MCore.Real.P01SourceCopyMachine.sourceCopyTimeBound_poly
#print axioms MCore.Real.P01SourceCopyMachine.sourceCopy_empty
#print axioms MCore.Real.P01SourceCopyMachine.sourceCopy_first_false
#print axioms MCore.Real.P01SourceCopyMachine.sourceCopy_first_true

end P01SourceCopyMachine
end Real
end MCore
