import MCore.Real.P01FullVerifierPhysicalStackV2
import MCore.Real.P01FullVerifierPhysicalMoves
import MCore.Real.P01FullVerifierPhysicalShuttles

namespace MCore
namespace Real
namespace P01FullVerifierInputShuttleV2

open CanonicalFinalProof
open P01FullVerifierPhysicalStackV2
open P01FullVerifierPhysicalMoves
open P01FullVerifierPhysicalShuttles

/-- Exact number of left moves from the V2 stack blank to witness[i].
The offset includes current stack cells, the stack/source blank, the source,
the source/witness blank, and finally the selected witness cell. -/
def witnessOffsetV2 (stack : List Bool) (source : BitString) (i : Nat) : Nat :=
  stack.length + source.length + 3 + i

def moveToWitnessSeqV2
    (stack : List Bool) (source : BitString) (i : Nat) : List Direction :=
  moveLeftSeq (witnessOffsetV2 stack source i)

def moveBackToStackSeqV2
    (stack : List Bool) (source : BitString) (i : Nat) : List Direction :=
  moveRightSeq (witnessOffsetV2 stack source i)

theorem moveToWitnessSeqV2_length
    (stack : List Bool) (source : BitString) (i : Nat) :
    (moveToWitnessSeqV2 stack source i).length =
      witnessOffsetV2 stack source i := by
  simp [moveToWitnessSeqV2, witnessOffsetV2, moveLeftSeq_length]

theorem witnessOffsetV2_positive
    (stack : List Bool) (source : BitString) (i : Nat) :
    0 < witnessOffsetV2 stack source i := by
  simp [witnessOffsetV2]
  omega

/-- The V2 left region has the exact prefix shape required by the generic
separator+witness indexing lemma. -/
theorem stackV2_left_as_prefix
    (witness source : BitString) (stack : List Bool) (padding : Nat) :
    (physicalStackV2Tape witness source stack padding).left =
      (stack.map some ++ none :: source.reverse.map some) ++
        none :: witness.map some := by
  simp [physicalStackV2Tape, List.append_assoc]

/-- Physical input lookup: after the exact left shuttle, the head is witness[i]. -/
theorem moveToWitnessSeqV2_head_correct
    (witness source : BitString)
    (stack : List Bool) (padding i : Nat)
    (hi : i < witness.length) :
    (execMoves none (moveToWitnessSeqV2 stack source i)
      (physicalStackV2Tape witness source stack padding)).head =
      some witness[i] := by
  unfold moveToWitnessSeqV2 witnessOffsetV2
  rw [show stack.length + source.length + 3 + i =
      ((stack.map some ++ none :: source.reverse.map some).length + 1 + i) + 1 by
        simp; omega]
  rw [execMoves_moveLeftSeq_head_getD]
  rw [stackV2_left_as_prefix]
  exact getD_prefix_separator_witness
    (stack.map some ++ none :: source.reverse.map some) witness i hi

theorem witness_roundTripV2_length
    (stack : List Bool) (source : BitString) (i : Nat) :
    (moveToWitnessSeqV2 stack source i ++
      moveBackToStackSeqV2 stack source i).length =
      2 * witnessOffsetV2 stack source i := by
  simp [moveToWitnessSeqV2, moveBackToStackSeqV2,
    moveLeftSeq_length, moveRightSeq_length, witnessOffsetV2]
  omega

theorem moveToWitnessSeqV2_legal
    (stack : List Bool) (source : BitString) (i : Nat) :
    LegalMoveSeq (moveToWitnessSeqV2 stack source i) := by
  exact moveLeftSeq_legal _

theorem moveBackToStackSeqV2_legal
    (stack : List Bool) (source : BitString) (i : Nat) :
    LegalMoveSeq (moveBackToStackSeqV2 stack source i) := by
  exact moveRightSeq_legal _

#print axioms MCore.Real.P01FullVerifierInputShuttleV2.moveToWitnessSeqV2_head_correct
#print axioms MCore.Real.P01FullVerifierInputShuttleV2.witness_roundTripV2_length
#print axioms MCore.Real.P01FullVerifierInputShuttleV2.moveToWitnessSeqV2_legal

end P01FullVerifierInputShuttleV2
end Real
end MCore
