import MCore.Real.CanonicalSATTagConsumerMachine
import MCore.Real.CanonicalSATFrameMachineV2

namespace MCore
namespace Real
namespace CanonicalSATParserTapeLayout

open CanonicalFinalProof
open CanonicalSATFrameAttack

/-- Unary outstanding-slot counter stored entirely on tape. -/
def slotCells (slots : Nat) : List (Option Bool) :=
  List.replicate slots (some true)

@[simp] theorem slotCells_length (slots : Nat) :
    (slotCells slots).length = slots := by
  simp [slotCells]

/--
Canonical parser boundary layout.

The already-consumed prefix is represented only by blank cells on the left.
If unread input remains, the head is its first bit and the rest is followed by
one blank delimiter and then the unary slot counter.
If unread input is empty, the head itself is the delimiter and the right side
is exactly the slot counter.

No symbol outside Option Bool is introduced.
-/
def parserBoundaryTape
    (leftBlankCount : Nat)
    (unread : BitString)
    (slots : Nat) :
    Tape (Option Bool) :=
  match unread with
  | [] =>
      { left := List.replicate leftBlankCount none
        head := none
        right := slotCells slots }
  | b :: bs =>
      { left := List.replicate leftBlankCount none
        head := some b
        right := bs.map some ++ none :: slotCells slots }

theorem parserBoundary_left_blank_padding
    (leftBlankCount : Nat)
    (unread : BitString)
    (slots : Nat) :
    CanonicalSATFrameMachineV2.LeftBlankPadding
      (parserBoundaryTape leftBlankCount unread slots) := by
  cases unread <;>
    simp [CanonicalSATFrameMachineV2.LeftBlankPadding, parserBoundaryTape]

theorem readTapeCells_map_some_until_blank
    (bits : BitString)
    (suffix : List (Option Bool)) :
    readTapeCells (bits.map some ++ none :: suffix) = bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bs ih =>
      simp [readTapeCells, ih]

/--
The semantic visible word at a parser boundary is exactly the unread input.
The slot counter is hidden behind the first blank delimiter and therefore
cannot be mistaken for source bits by the existing tapeWord semantics.
-/
theorem tapeWord_parserBoundaryTape
    (leftBlankCount : Nat)
    (unread : BitString)
    (slots : Nat) :
    tapeWord (parserBoundaryTape leftBlankCount unread slots) = unread := by
  cases unread with
  | nil =>
      rfl
  | cons b bs =>
      simp [parserBoundaryTape, tapeWord,
        readTapeCells_map_some_until_blank]

/-- The zero-slot/empty-input accepting boundary has no data to the right. -/
@[simp] theorem parserBoundary_empty_zero
    (leftBlankCount : Nat) :
    parserBoundaryTape leftBlankCount [] 0 =
      { left := List.replicate leftBlankCount none
        head := none
        right := [] } := by
  rfl

/-- Slot update for one consumed prefix token. -/
def updateSlots (slots arity : Nat) : Option Nat :=
  match slots with
  | 0 => none
  | s + 1 => some (s + arity)

@[simp] theorem updateSlots_leaf (s : Nat) :
    updateSlots (s + 1) 0 = some s := by
  simp [updateSlots]

@[simp] theorem updateSlots_unary (s : Nat) :
    updateSlots (s + 1) 1 = some (s + 1) := by
  simp [updateSlots]

@[simp] theorem updateSlots_binary (s : Nat) :
    updateSlots (s + 1) 2 = some (s + 2) := by
  simp [updateSlots]

@[simp] theorem updateSlots_zero (arity : Nat) :
    updateSlots 0 arity = none := by
  simp [updateSlots]

/-- Boundary classification after a complete token update. -/
inductive BoundaryDisposition where
  | accept
  | continue
  | reject
  deriving DecidableEq, Repr

def classifyBoundary (unread : BitString) (slots : Nat) :
    BoundaryDisposition :=
  match unread, slots with
  | [], 0 => .accept
  | [], _ + 1 => .reject
  | _ :: _, 0 => .reject
  | _ :: _, _ + 1 => .continue

@[simp] theorem classifyBoundary_accept_iff
    (unread : BitString) (slots : Nat) :
    classifyBoundary unread slots = .accept ↔ unread = [] ∧ slots = 0 := by
  cases unread <;> cases slots <;> simp [classifyBoundary]

@[simp] theorem classifyBoundary_continue_iff
    (unread : BitString) (slots : Nat) :
    classifyBoundary unread slots = .continue ↔
      unread ≠ [] ∧ 0 < slots := by
  cases unread <;> cases slots <;> simp [classifyBoundary]

@[simp] theorem classifyBoundary_reject_iff
    (unread : BitString) (slots : Nat) :
    classifyBoundary unread slots = .reject ↔
      (unread = [] ∧ 0 < slots) ∨
      (unread ≠ [] ∧ slots = 0) := by
  cases unread <;> cases slots <;> simp [classifyBoundary]

/--
At every boundary exactly one of accept/continue/reject is selected.
This is the finite-control decision that the final parser TM must implement.
-/
theorem boundary_disposition_total
    (unread : BitString) (slots : Nat) :
    classifyBoundary unread slots = .accept ∨
    classifyBoundary unread slots = .continue ∨
    classifyBoundary unread slots = .reject := by
  cases unread <;> cases slots <;> simp [classifyBoundary]

#print axioms MCore.Real.CanonicalSATParserTapeLayout.slotCells_length
#print axioms MCore.Real.CanonicalSATParserTapeLayout.parserBoundary_left_blank_padding
#print axioms MCore.Real.CanonicalSATParserTapeLayout.tapeWord_parserBoundaryTape
#print axioms MCore.Real.CanonicalSATParserTapeLayout.updateSlots_leaf
#print axioms MCore.Real.CanonicalSATParserTapeLayout.classifyBoundary_accept_iff
#print axioms MCore.Real.CanonicalSATParserTapeLayout.classifyBoundary_continue_iff
#print axioms MCore.Real.CanonicalSATParserTapeLayout.classifyBoundary_reject_iff
#print axioms MCore.Real.CanonicalSATParserTapeLayout.boundary_disposition_total

end CanonicalSATParserTapeLayout
end Real
end MCore
