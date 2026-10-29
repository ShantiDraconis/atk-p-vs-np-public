import MCore.Real.P01FullVerifierInputShuttleV2

namespace MCore
namespace Real
namespace P01PreservingWitnessRoundTrip

open CanonicalFinalProof
open P01FullVerifierPhysicalMoves
open P01FullVerifierPhysicalStackV2
open P01FullVerifierInputShuttleV2

theorem execMoves_append {Symbol : Type}
    (blank : Symbol) (xs ys : List Direction) (t : Tape Symbol) :
    execMoves blank (xs ++ ys) t =
      execMoves blank ys (execMoves blank xs t) := by
  induction xs generalizing t with
  | nil =>
      rfl
  | cons d ds ih =>
      simp only [List.cons_append, execMoves_cons]
      exact ih (Tape.move blank d t)

theorem move_left_right_cancel {Symbol : Type}
    (blank : Symbol) (t : Tape Symbol)
    (hleft : t.left ≠ []) :
    Tape.move blank .right (Tape.move blank .left t) = t := by
  rcases t with ⟨left, head, right⟩
  cases left with
  | nil =>
      exact False.elim (hleft rfl)
  | cons x xs =>
      rfl

theorem execMoves_left_right_roundTrip {Symbol : Type}
    (blank : Symbol) (n : Nat) (t : Tape Symbol)
    (hbound : n ≤ t.left.length) :
    execMoves blank (moveRightSeq n)
      (execMoves blank (moveLeftSeq n) t) = t := by
  induction n generalizing t with
  | zero =>
      rfl
  | succ n ih =>
      have hleft : t.left ≠ [] := by
        intro hnil
        rw [hnil] at hbound
        simp at hbound
      have htail :
          n ≤ (Tape.move blank .left t).left.length := by
        rcases t with ⟨left, head, right⟩
        cases left with
        | nil =>
            simp at hbound
        | cons x xs =>
            simp [Tape.move] at hbound ⊢
            omega
      rw [show moveLeftSeq (n + 1) = .left :: moveLeftSeq n by
        simp [moveLeftSeq, List.replicate_succ]]
      simp only [execMoves_cons]
      have hright :
          moveRightSeq (n + 1) = moveRightSeq n ++ [.right] := by
        unfold moveRightSeq
        induction n with
        | zero =>
            rfl
        | succ n ihn =>
            simp [List.replicate_succ, ihn]
      rw [hright]
      rw [execMoves_append]
      rw [ih (Tape.move blank .left t) htail]
      simpa [execMoves] using move_left_right_cancel blank t hleft

/-- The existing V2 witness shuttle is non-destructive at the tape level:
it reads witness[i], and the exact inverse shuttle restores the complete
physical stack/source/witness tape. -/
theorem witness_roundTripV2_preserves_tape
    (witness source : BitString)
    (stack : List Bool) (padding i : Nat)
    (hi : i < witness.length) :
    let start := physicalStackV2Tape witness source stack padding
    let atWitness :=
      execMoves none (moveToWitnessSeqV2 stack source i) start
    atWitness.head = some witness[i] /\
      execMoves none (moveBackToStackSeqV2 stack source i) atWitness = start := by
  dsimp
  constructor
  · exact moveToWitnessSeqV2_head_correct
      witness source stack padding i hi
  · unfold moveToWitnessSeqV2 moveBackToStackSeqV2
    apply execMoves_left_right_roundTrip
    simp [physicalStackV2Tape, witnessOffsetV2]
    omega

#print axioms MCore.Real.P01PreservingWitnessRoundTrip.witness_roundTripV2_preserves_tape

end P01PreservingWitnessRoundTrip
end Real
end MCore
