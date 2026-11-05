import MCore.Real.P01FullVerifierPhysicalStackV2
import MCore.Real.P01FullVerifierPhysicalMoves

namespace MCore
namespace Real
namespace P01SourceCursorInvariant

open CanonicalFinalProof
open P01FullVerifierPhysicalStackV2
open P01FullVerifierPhysicalMoves

/-- Number of left moves from the canonical V2 stack-end blank to the first
source bit.  The stack is nearest the head, followed by one stack/source blank,
then the reversed source. -/
def sourceStartOffset (stack : List Bool) (source : BitString) : Nat :=
  stack.length + source.length + 1

def moveToSourceStartSeq (stack : List Bool) (source : BitString) :
    List Direction :=
  moveLeftSeq (sourceStartOffset stack source)

def moveBackToStackEndSeq (stack : List Bool) (source : BitString) :
    List Direction :=
  moveRightSeq (sourceStartOffset stack source)

theorem moveToSourceStartSeq_length
    (stack : List Bool) (source : BitString) :
    (moveToSourceStartSeq stack source).length =
      sourceStartOffset stack source := by
  simp [moveToSourceStartSeq, sourceStartOffset, moveLeftSeq_length]

theorem moveBackToStackEndSeq_length
    (stack : List Bool) (source : BitString) :
    (moveBackToStackEndSeq stack source).length =
      sourceStartOffset stack source := by
  simp [moveBackToStackEndSeq, sourceStartOffset, moveRightSeq_length]

theorem getD_append_head
    {α : Type} (pre : List α) (x d : α) (tail : List α) :
    (pre ++ x :: tail).getD pre.length d = x := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
      simpa [List.getD_cons_succ] using ih

/-- On every nonempty canonical source, the exact left shuttle lands on the
first source bit while preserving the represented tape contents. -/
theorem moveToSourceStart_head_correct
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (stack : List Bool) (padding : Nat) :
    (execMoves none (moveToSourceStartSeq stack (b :: bs))
      (physicalStackV2Tape witness (b :: bs) stack padding)).head =
      some b := by
  unfold moveToSourceStartSeq sourceStartOffset
  rw [show stack.length + (b :: bs).length + 1 =
      (stack.length + bs.length + 1) + 1 by simp; omega]
  rw [execMoves_moveLeftSeq_head_getD]
  have hidx :
      stack.length + bs.length + 1 =
        (stack.map some ++ none :: (bs.map some).reverse).length := by
    simp
    omega
  rw [hidx]
  simpa [physicalStackV2Tape, List.map_reverse, List.append_assoc] using
    (getD_append_head
      (stack.map some ++ none :: (bs.map some).reverse)
      (some b) none (none :: witness.map some))

/-- The source cursor motion is legal in the same primitive-move sense used by
all prior certified P01 shuttles. -/
theorem moveToSourceStartSeq_legal
    (stack : List Bool) (source : BitString) :
    LegalMoveSeq (moveToSourceStartSeq stack source) := by
  exact moveLeftSeq_legal _



/-- Sequential execution respects list concatenation. -/
theorem execMoves_append
    {Symbol : Type}
    (blank : Symbol)
    (xs ys : List Direction)
    (t : Tape Symbol) :
    execMoves blank (xs ++ ys) t =
      execMoves blank ys (execMoves blank xs t) := by
  induction xs generalizing t with
  | nil => rfl
  | cons d ds ih =>
      simp [execMoves, ih]

/-- Repeated right moves can be exposed at the end of the list. -/
theorem moveRightSeq_succ_last (n : Nat) :
    moveRightSeq (Nat.succ n) =
      moveRightSeq n ++ [.right] := by
  unfold moveRightSeq
  simpa [Nat.succ_eq_add_one] using
    (List.replicate_succ' :
      List.replicate (n + 1) Direction.right =
        List.replicate n Direction.right ++ [Direction.right])

/-- Exact cancellation on the local tape representation requires that the left
shuttle never runs past the represented left list.  This is the truthful
version of the round-trip law for the project's explicit-blank tape model. -/
theorem execMoves_left_right_cancel
    (n : Nat) (t : Tape (Option Bool))
    (hbound : n ≤ t.left.length) :
    execMoves none (moveLeftSeq n ++ moveRightSeq n) t = t := by
  induction n generalizing t with
  | zero =>
      rfl
  | succ n ih =>
      rcases t with ⟨left, head, right⟩
      cases left with
      | nil =>
          simp at hbound
      | cons next rest =>
          have hn : n ≤ rest.length := by
            simp at hbound
            omega
          rw [show moveLeftSeq (Nat.succ n) =
              .left :: moveLeftSeq n by rfl]
          rw [moveRightSeq_succ_last]
          simp only [List.cons_append, execMoves]
          change
            execMoves none
              (moveLeftSeq n ++ (moveRightSeq n ++ [.right]))
              { left := rest, head := next, right := head :: right } =
            { left := next :: rest, head := head, right := right }
          rw [← List.append_assoc]
          rw [execMoves_append]
          rw [ih _ hn]
          rfl

/-- The canonical V2 layout always contains enough represented cells to reach
the first source position without crossing the left boundary. -/
theorem sourceStartOffset_le_left_length
    (witness source : BitString)
    (stack : List Bool) (padding : Nat) :
    sourceStartOffset stack source ≤
      (physicalStackV2Tape witness source stack padding).left.length := by
  simp [sourceStartOffset, physicalStackV2Tape]
  omega

/-- The complete P01 source-cursor shuttle is exactly reversible: after visiting
the first source bit and returning by the matching right shuttle, witness,
source, frame stack and padding are all restored byte-for-byte. -/
theorem source_cursor_roundTrip_tape
    (witness source : BitString)
    (stack : List Bool) (padding : Nat) :
    execMoves none
      (moveToSourceStartSeq stack source ++
        moveBackToStackEndSeq stack source)
      (physicalStackV2Tape witness source stack padding) =
    physicalStackV2Tape witness source stack padding := by
  unfold moveToSourceStartSeq moveBackToStackEndSeq
  exact execMoves_left_right_cancel
    (sourceStartOffset stack source)
    (physicalStackV2Tape witness source stack padding)
    (sourceStartOffset_le_left_length witness source stack padding)


/-- The return shuttle has exactly the same cost envelope. -/
theorem source_cursor_roundTrip_length
    (stack : List Bool) (source : BitString) :
    (moveToSourceStartSeq stack source ++
      moveBackToStackEndSeq stack source).length =
      2 * sourceStartOffset stack source := by
  rw [List.length_append, moveToSourceStartSeq_length,
    moveBackToStackEndSeq_length]
  omega

#print axioms MCore.Real.P01SourceCursorInvariant.moveToSourceStart_head_correct
#print axioms MCore.Real.P01SourceCursorInvariant.execMoves_left_right_cancel
#print axioms MCore.Real.P01SourceCursorInvariant.source_cursor_roundTrip_tape
#print axioms MCore.Real.P01SourceCursorInvariant.source_cursor_roundTrip_length

end P01SourceCursorInvariant
end Real
end MCore
