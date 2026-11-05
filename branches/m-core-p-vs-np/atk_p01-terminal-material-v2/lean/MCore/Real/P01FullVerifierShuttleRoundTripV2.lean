import MCore.Real.P01FullVerifierInputShuttleV2
import MCore.Real.P01FullVerifierShuttleReturn

namespace MCore
namespace Real
namespace P01FullVerifierShuttleRoundTripV2

open CanonicalFinalProof
open P01FullVerifierPhysicalMoves
open P01FullVerifierPhysicalStackV2
open P01FullVerifierInputShuttleV2
open P01FullVerifierShuttleReturn

theorem replicate_succ_append
    {α : Type} (x : α) (n : Nat) :
    List.replicate (n + 1) x = List.replicate n x ++ [x] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate_succ, ih]

/-- Repeating n legal left moves and then n right moves restores the exact
original tape whenever the original left side contains at least n cells. -/
theorem left_right_roundtrip
    {Symbol : Type}
    (blank : Symbol)
    (n : Nat)
    (t : Tape Symbol)
    (h : n ≤ t.left.length) :
    execMoves blank (moveRightSeq n)
      (execMoves blank (moveLeftSeq n) t) = t := by
  induction n generalizing t with
  | zero =>
      rfl
  | succ n ih =>
      cases t with
      | mk left head right =>
          cases left with
          | nil =>
              simp at h
          | cons x xs =>
              have hs : Nat.succ n ≤ Nat.succ xs.length := by
                simpa using h
              have hn : n ≤ xs.length :=
                Nat.le_of_succ_le_succ hs
              let tLeft : Tape Symbol :=
                { left := xs, head := x, right := head :: right }
              have hi :
                  execMoves blank (moveRightSeq n)
                    (execMoves blank (moveLeftSeq n) tLeft) = tLeft :=
                ih tLeft hn
              have hl :
                  moveLeftSeq (Nat.succ n) =
                    .left :: moveLeftSeq n := by
                simp [moveLeftSeq, List.replicate_succ]
              have hr :
                  moveRightSeq (Nat.succ n) =
                    moveRightSeq n ++ [.right] := by
                unfold moveRightSeq
                simpa [Nat.succ_eq_add_one] using
                  (replicate_succ_append Direction.right n)
              rw [hl, execMoves_cons]
              change
                execMoves blank (moveRightSeq (Nat.succ n))
                  (execMoves blank (moveLeftSeq n) tLeft) =
                    { left := x :: xs, head := head, right := right }
              rw [hr, execMoves_append]
              rw [hi]
              simp [execMoves, tLeft, Tape.move]

/-- The witness shuttle never needs to cross beyond the concrete V2 left
region when the requested witness index is valid. -/
theorem witnessOffsetV2_le_left_length
    (witness source : BitString)
    (stack : List Bool)
    (padding i : Nat)
    (hi : i < witness.length) :
    witnessOffsetV2 stack source i ≤
      (physicalStackV2Tape witness source stack padding).left.length := by
  simp [witnessOffsetV2, physicalStackV2Tape]
  omega

/-- After reading a valid witness cell, the exact inverse shuttle restores the
same physical stack tape bit-for-bit. -/
theorem witness_roundTripV2_exec
    (witness source : BitString)
    (stack : List Bool)
    (padding i : Nat)
    (hi : i < witness.length) :
    execMoves none (moveBackToStackSeqV2 stack source i)
      (execMoves none (moveToWitnessSeqV2 stack source i)
        (physicalStackV2Tape witness source stack padding)) =
      physicalStackV2Tape witness source stack padding := by
  have hbound :=
    witnessOffsetV2_le_left_length witness source stack padding i hi
  simpa [moveToWitnessSeqV2, moveBackToStackSeqV2] using
    (left_right_roundtrip
      (blank := (none : Option Bool))
      (n := witnessOffsetV2 stack source i)
      (t := physicalStackV2Tape witness source stack padding)
      hbound)

/-- The complete physical input macro both reads the correct assignment bit
and returns to the unchanged evaluator stack layout. -/
theorem witness_read_and_return_correct
    (witness source : BitString)
    (stack : List Bool)
    (padding i : Nat)
    (hi : i < witness.length) :
    let moved :=
      execMoves none (moveToWitnessSeqV2 stack source i)
        (physicalStackV2Tape witness source stack padding)
    moved.head = some witness[i] ∧
      execMoves none (moveBackToStackSeqV2 stack source i) moved =
        physicalStackV2Tape witness source stack padding := by
  dsimp
  constructor
  · exact moveToWitnessSeqV2_head_correct
      witness source stack padding i hi
  · exact witness_roundTripV2_exec
      witness source stack padding i hi

#print axioms MCore.Real.P01FullVerifierShuttleRoundTripV2.left_right_roundtrip
#print axioms MCore.Real.P01FullVerifierShuttleRoundTripV2.witness_roundTripV2_exec
#print axioms MCore.Real.P01FullVerifierShuttleRoundTripV2.witness_read_and_return_correct

end P01FullVerifierShuttleRoundTripV2
end Real
end MCore
