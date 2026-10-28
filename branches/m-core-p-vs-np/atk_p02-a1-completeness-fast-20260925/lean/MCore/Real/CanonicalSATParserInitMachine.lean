import MCore.Real.CanonicalSATParserTapeLayout

namespace MCore
namespace Real
namespace CanonicalSATParserInitMachine

open CanonicalFinalProof
open CanonicalSATParserTapeLayout

/--
Five-state initializer:
0 scans to the implicit blank after the input;
1 writes the initial unary slot counter cell to the right of the delimiter;
2 crosses back over the delimiter;
3 rewinds across the original input to the left boundary;
4 is the halting state positioned at the first unread input bit (or the
delimiter for empty input).

The machine never stores input length or syntax in control.
-/
def parserInitMachine : TM (Fin 5) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some b => (0, some b, .right)
        | none => (1, none, .right)
      else if q = 1 then
        (2, some true, .left)
      else if q = 2 then
        (3, symbol, .left)
      else if q = 3 then
        match symbol with
        | some b => (3, some b, .left)
        | none => (4, none, .right)
      else
        (4, symbol, .stay)
    halting := fun q => q == 4 }

@[simp] theorem parserInit_blank_none :
    parserInitMachine.blank = none := rfl

@[simp] theorem parserInit_not_halted_0 :
    parserInitMachine.halting (0 : Fin 5) = false := by rfl

@[simp] theorem parserInit_not_halted_1 :
    parserInitMachine.halting (1 : Fin 5) = false := by rfl

@[simp] theorem parserInit_not_halted_2 :
    parserInitMachine.halting (2 : Fin 5) = false := by rfl

@[simp] theorem parserInit_not_halted_3 :
    parserInitMachine.halting (3 : Fin 5) = false := by rfl

@[simp] theorem parserInit_halted_4 :
    parserInitMachine.halting (4 : Fin 5) = true := by rfl

/-- Conservative exact runtime budget for initialization. -/
def parserInitTimeBound : TimeBound :=
  fun n => 2 * n + 4

theorem parserInitTimeBound_poly :
    PolynomialTimeBound parserInitTimeBound := by
  refine ⟨6, 1, ?_⟩
  intro n
  simp [parserInitTimeBound]
  omega

/-- State 0 preserves each source bit while scanning right. -/
theorem parserInit_scan_bit
    (left : List (Option Bool))
    (b : Bool)
    (rest : List (Option Bool)) :
    parserInitMachine.step
      { state := (0 : Fin 5)
        tape := { left := left, head := some b, right := rest } } =
      { state := (0 : Fin 5)
        tape :=
          match rest with
          | [] =>
              { left := some b :: left, head := none, right := [] }
          | next :: tail =>
              { left := some b :: left, head := next, right := tail } } := by
  cases rest <;>
    simp [parserInitMachine, TM.step, Tape.write, Tape.move]

/-- At the input-end blank, state 0 crosses to the fresh cell on the right. -/
theorem parserInit_cross_end
    (left : List (Option Bool)) :
    parserInitMachine.step
      { state := (0 : Fin 5)
        tape := { left := left, head := none, right := [] } } =
      { state := (1 : Fin 5)
        tape := { left := none :: left, head := none, right := [] } } := by
  simp [parserInitMachine, TM.step, Tape.write, Tape.move]

/-- State 1 writes the initial one-cell unary slot counter and returns left. -/
theorem parserInit_write_one_slot
    (left : List (Option Bool)) :
    parserInitMachine.step
      { state := (1 : Fin 5)
        tape := { left := none :: left, head := none, right := [] } } =
      { state := (2 : Fin 5)
        tape := { left := left, head := none, right := [some true] } } := by
  simp [parserInitMachine, TM.step, Tape.write, Tape.move]

/-- The intended initialized boundary uses one slot and only Option Bool data. -/
def initializedBoundary (bits : BitString) : Tape (Option Bool) :=
  parserBoundaryTape 1 bits 1

@[simp] theorem initializedBoundary_word
    (bits : BitString) :
    CanonicalSATFrameAttack.tapeWord (initializedBoundary bits) = bits := by
  exact tapeWord_parserBoundaryTape 1 bits 1

@[simp] theorem initializedBoundary_slot_count :
    (slotCells 1).length = 1 := by
  simp [slotCells]

#print axioms MCore.Real.CanonicalSATParserInitMachine.parserInit_blank_none
#print axioms MCore.Real.CanonicalSATParserInitMachine.parserInitTimeBound_poly
#print axioms MCore.Real.CanonicalSATParserInitMachine.parserInit_scan_bit
#print axioms MCore.Real.CanonicalSATParserInitMachine.parserInit_cross_end
#print axioms MCore.Real.CanonicalSATParserInitMachine.parserInit_write_one_slot
#print axioms MCore.Real.CanonicalSATParserInitMachine.initializedBoundary_word

end CanonicalSATParserInitMachine
end Real
end MCore
