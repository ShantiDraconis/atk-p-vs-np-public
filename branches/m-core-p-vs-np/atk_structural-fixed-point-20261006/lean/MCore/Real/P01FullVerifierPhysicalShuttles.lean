import MCore.Real.P01FullVerifierPhysicalMoves
import MCore.Real.P01FullVerifierPhysical

namespace MCore
namespace Real
namespace P01FullVerifierPhysicalShuttles

open CanonicalFinalProof
open P01FullVerifierPhysicalMoves

/-- Source-end layout reached by the certified physical scanner.  The left
list is nearest-head first: reversed source, separator, then witness bits. -/
def sourceEndTape (witness source : BitString) : Tape (Option Bool) :=
  { left := source.reverse.map some ++ none :: witness.map some
    head := none
    right := [] }

/-- Exact number of primitive left moves from the source-end blank to
witness[i]. -/
def witnessOffset (source : BitString) (i : Nat) : Nat :=
  source.length + 2 + i

def moveToWitnessSeq (source : BitString) (i : Nat) : List Direction :=
  moveLeftSeq (witnessOffset source i)

/-- Returning from witness[i] to the source-end stack position uses the same
number of primitive right moves. -/
def moveToStackSeq (source : BitString) (i : Nat) : List Direction :=
  moveRightSeq (witnessOffset source i)

theorem moveToWitnessSeq_length (source : BitString) (i : Nat) :
    (moveToWitnessSeq source i).length = witnessOffset source i := by
  simp [moveToWitnessSeq, witnessOffset, moveLeftSeq_length]

theorem moveToStackSeq_length (source : BitString) (i : Nat) :
    (moveToStackSeq source i).length = witnessOffset source i := by
  simp [moveToStackSeq, witnessOffset, moveRightSeq_length]

theorem moveToWitnessSeq_legal (source : BitString) (i : Nat) :
    LegalMoveSeq (moveToWitnessSeq source i) := by
  exact moveLeftSeq_legal _

theorem moveToStackSeq_legal (source : BitString) (i : Nat) :
    LegalMoveSeq (moveToStackSeq source i) := by
  exact moveRightSeq_legal _

theorem sourceEndTape_left_length (witness source : BitString) :
    (sourceEndTape witness source).left.length =
      source.length + 1 + witness.length := by
  simp [sourceEndTape]
  omega

theorem witness_map_getD
    (witness : BitString) (i : Nat) (hi : i < witness.length) :
    (witness.map some).getD i none = some witness[i] := by
  induction witness generalizing i with
  | nil =>
      simp at hi
  | cons b bs ih =>
      cases i with
      | zero =>
          simp
      | succ i =>
          have hi' : i < bs.length := by
            simpa using hi
          simpa using ih i hi'

theorem getD_prefix_separator_witness
    (base : List (Option Bool)) (witness : BitString)
    (i : Nat) (hi : i < witness.length) :
    (base ++ none :: witness.map some).getD (base.length + 1 + i) none =
      some witness[i] := by
  induction base with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.zero_add]
      change (none :: witness.map some).getD (1 + i) none = some witness[i]
      simpa [Nat.add_comm, List.getD_cons_succ] using
        witness_map_getD witness i hi
  | cons x xs ih =>
      simp only [List.cons_append, List.length_cons]
      change (x :: (xs ++ none :: witness.map some)).getD
        (Nat.succ xs.length + 1 + i) none = some witness[i]
      simpa [List.getD_cons_succ, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using ih

/-- A valid witness index is physically present before the left shuttle can
run off the represented witness region. -/
theorem witnessOffset_le_left_length
    (witness source : BitString) (i : Nat) (hi : i < witness.length) :
    witnessOffset source i ≤ (sourceEndTape witness source).left.length := by
  rw [sourceEndTape_left_length]
  unfold witnessOffset
  omega


/-- Concrete witness targeting: after the exact left shuttle from source-end,
the head contains witness[i].  This replaces any abstract head-position axiom. -/
theorem moveToWitnessSeq_head_correct
    (witness source : BitString) (i : Nat) (hi : i < witness.length) :
    (execMoves none (moveToWitnessSeq source i)
      (sourceEndTape witness source)).head = some witness[i] := by
  unfold moveToWitnessSeq witnessOffset
  rw [show source.length + 2 + i = (source.length + 1 + i) + 1 by omega]
  rw [execMoves_moveLeftSeq_head_getD]
  unfold sourceEndTape
  simpa using
    getD_prefix_separator_witness (source.reverse.map some) witness i hi

/-- The complete witness round-trip has linear shuttle cost in source length
plus the selected witness index. -/
theorem witness_roundTrip_length
    (source : BitString) (i : Nat) :
    (moveToWitnessSeq source i ++ moveToStackSeq source i).length =
      2 * witnessOffset source i := by
  rw [List.length_append, moveToWitnessSeq_length, moveToStackSeq_length]
  omega

#print axioms MCore.Real.P01FullVerifierPhysicalShuttles.witnessOffset_le_left_length
#print axioms MCore.Real.P01FullVerifierPhysicalShuttles.moveToWitnessSeq_head_correct
#print axioms MCore.Real.P01FullVerifierPhysicalShuttles.witness_roundTrip_length

end P01FullVerifierPhysicalShuttles
end Real
end MCore
