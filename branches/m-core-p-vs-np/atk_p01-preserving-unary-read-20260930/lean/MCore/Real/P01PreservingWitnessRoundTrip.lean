import MCore.Real.P01FullVerifierInputShuttleV2

namespace MCore
namespace Real
namespace P01PreservingWitnessRoundTrip

open CanonicalFinalProof
open P01FullVerifierPhysicalMoves
open P01FullVerifierPhysicalStackV2
open P01FullVerifierInputShuttleV2

theorem move_left_right_cancel
    {Symbol : Type}
    (blank : Symbol)
    (t : Tape Symbol)
    (hleft : t.left ≠ []) :
    Tape.move blank .right (Tape.move blank .left t) = t := by
  cases t with
  | mk left head right =>
      cases left with
      | nil =>
          simp at hleft
      | cons a rest =>
          simp [Tape.move]

theorem execMoves_repeat_commute
    {Symbol : Type}
    (blank : Symbol)
    (d : Direction)
    (n : Nat)
    (t : Tape Symbol) :
    Tape.move blank d
        (execMoves blank (List.replicate n d) t) =
      execMoves blank (List.replicate n d)
        (Tape.move blank d t) := by
  induction n generalizing t with
  | zero =>
      rfl
  | succ n ih =>
      simp only [List.replicate_succ, execMoves_cons]
      rw [ih]
      rw [ih]

theorem left_right_roundTrip
    {Symbol : Type}
    (blank : Symbol)
    (n : Nat)
    (t : Tape Symbol)
    (hbound : n ≤ t.left.length) :
    execMoves blank (moveRightSeq n)
      (execMoves blank (moveLeftSeq n) t) = t := by
  induction n generalizing t with
  | zero =>
      rfl
  | succ n ih =>
      have hnonempty : t.left ≠ [] := by
        intro h
        rw [h] at hbound
        simp at hbound
      have htail :
          n ≤ (Tape.move blank .left t).left.length := by
        cases t with
        | mk left head right =>
            cases left with
            | nil =>
                simp at hnonempty
            | cons a rest =>
                simp [Tape.move] at hbound ⊢
                omega
      unfold moveLeftSeq moveRightSeq
      rw [List.replicate_succ, List.replicate_succ]
      simp only [execMoves_cons]
      rw [show
        execMoves blank (List.replicate n Direction.right)
          (Tape.move blank Direction.right
            (execMoves blank (List.replicate n Direction.left)
              (Tape.move blank Direction.left t))) =
        Tape.move blank Direction.right
          (execMoves blank (List.replicate n Direction.right)
            (execMoves blank (List.replicate n Direction.left)
              (Tape.move blank Direction.left t))) by
          symm
          exact execMoves_repeat_commute blank Direction.right n
            (execMoves blank (List.replicate n Direction.left)
              (Tape.move blank Direction.left t))]
      rw [ih (Tape.move blank .left t) htail]
      exact move_left_right_cancel blank t hnonempty

theorem witnessOffsetV2_le_left_length
    (witness source : BitString)
    (stack : List Bool)
    (padding i : Nat)
    (hi : i < witness.length) :
    witnessOffsetV2 stack source i ≤
      (physicalStackV2Tape witness source stack padding).left.length := by
  simp [witnessOffsetV2, physicalStackV2Tape]
  omega

/-- Exact non-destructive shuttle theorem.  The witness lookup uses only tape
moves: after reaching witness[i], returning by the same physical distance
restores the complete V2 tape byte-for-byte. -/
theorem witness_roundTripV2_preserves_tape
    (witness source : BitString)
    (stack : List Bool)
    (padding i : Nat)
    (hi : i < witness.length) :
    execMoves none
      (moveBackToStackSeqV2 stack source i)
      (execMoves none
        (moveToWitnessSeqV2 stack source i)
        (physicalStackV2Tape witness source stack padding)) =
      physicalStackV2Tape witness source stack padding := by
  exact left_right_roundTrip none
    (witnessOffsetV2 stack source i)
    (physicalStackV2Tape witness source stack padding)
    (witnessOffsetV2_le_left_length witness source stack padding i hi)

/-- The selected bit is physically read without modifying the tape. -/
theorem preserving_lookupV2
    (witness source : BitString)
    (stack : List Bool)
    (padding i : Nat)
    (hi : i < witness.length) :
    let start := physicalStackV2Tape witness source stack padding
    let atWitness :=
      execMoves none (moveToWitnessSeqV2 stack source i) start
    atWitness.head = some witness[i] ∧
      execMoves none (moveBackToStackSeqV2 stack source i) atWitness = start := by
  dsimp
  exact ⟨
    moveToWitnessSeqV2_head_correct witness source stack padding i hi,
    witness_roundTripV2_preserves_tape witness source stack padding i hi
  ⟩

#print axioms MCore.Real.P01PreservingWitnessRoundTrip.witness_roundTripV2_preserves_tape
#print axioms MCore.Real.P01PreservingWitnessRoundTrip.preserving_lookupV2

end P01PreservingWitnessRoundTrip
end Real
end MCore
