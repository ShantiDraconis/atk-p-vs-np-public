import MCore.Real.PNPDiscovery.LeftBlockElimination
import MCore.Real.SourceRecovery

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding
open SourceRecovery
open P02ComplementRunRealization
open P02TableauDynamics

/-- Number of encoded bits occupied by the first k CNF clauses, excluding the
recursive encoding of the remaining suffix. -/
def clauseBitOffset
    (F : NTMCNF)
    (k : Nat) : Nat :=
  (encodeCNFSpinePrefix (F.take k)).length

/-- Exact decomposition of an encoded CNF at a clause boundary. -/
theorem encode_ntmCNFCircuit_split_at
    (F : NTMCNF)
    (k : Nat) :
    encodeCircuit (ntmCNFCircuit F) =
      encodeCNFSpinePrefix (F.take k) ++
        encodeCircuit (ntmCNFCircuit (F.drop k)) := by
  have hsplit : F.take k ++ F.drop k = F :=
    List.take_append_drop k F
  rw [← hsplit]
  exact encode_ntmCNFCircuit_append (F.take k) (F.drop k)

/-- Therefore the first clauseBitOffset bits are literally the encoded spine
of the first k clauses. -/
theorem take_clauseBitOffset
    (F : NTMCNF)
    (k : Nat) :
    (encodeCircuit (ntmCNFCircuit F)).take
        (clauseBitOffset F k) =
      encodeCNFSpinePrefix (F.take k) := by
  rw [encode_ntmCNFCircuit_split_at F k]
  simp [clauseBitOffset]

/-- Clause index of source/right cell i in the time-zero tableau. -/
def sourceCellClauseOffset
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat) : Nat :=
  rightBlockOffset M x.length t + 3 * i

/-- Bit index at which the CNF encoding reaches source/right cell i. -/
def sourceCellBitOffset
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat) : Nat :=
  clauseBitOffset
    (ntmInitialCNF M x t)
    (sourceCellClauseOffset M x t i)

/-- The certified source-recovery offset theorem identifies exactly the
three-clause block beginning at sourceCellClauseOffset. -/
theorem sourceCell_clause_slice
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t) :
    symbolBlockAt
        (ntmInitialCNF M x t)
        (sourceCellClauseOffset M x t i) =
      initialRightCellBlock M x t i := by
  simpa [sourceCellClauseOffset,
    initialRightCellBlock, sourceRightSymbol] using
    (drop_rightBlockOffset_take_right M x t i hi)

/-- Prefix immediately before source cell i is now a literal
bitstring quantity.  Visibility must be measured against the clock on the
actual complemented Cook--Levin output, not merely its initial CNF prefix. -/
def sourceCellVisibleInReduction
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString)
    (i : Nat) : Prop :=
  sourceCellBitOffset
      (complementToNTMCandidate M)
      x
      (M.timeBound x.length)
      i <
    M.timeBound (R_M M hTotal x).length + 1

/-- Visibility is now exactly the arithmetic comparison used by the candidate
read cone on R_M(x). -/
theorem sourceCellVisibleInReduction_iff
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString)
    (i : Nat) :
    sourceCellVisibleInReduction M hTotal x i ↔
      sourceCellBitOffset
          (complementToNTMCandidate M)
          x
          (M.timeBound x.length)
          i <
        M.timeBound (R_M M hTotal x).length + 1 := by
  rfl

/-- Exact numeric frontier for one source cell: either the candidate's read
cone reaches the encoded cell boundary, or it does not. -/
theorem sourceCell_visible_or_hidden
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString)
    (i : Nat) :
    sourceCellVisibleInReduction M hTotal x i ∨
      M.timeBound (R_M M hTotal x).length + 1 ≤
        sourceCellBitOffset
          (complementToNTMCandidate M)
          x
          (M.timeBound x.length)
          i := by
  omega

/-- The full complemented reduction retains the complete source, with no
semantic assumption beyond the already-certified concrete reduction. -/
theorem reduction_source_recoverable
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    decodeSourceBits
        (complementToNTMCandidate M)
        x.length
        (M.timeBound x.length)
        (R_M M hTotal x) =
      some x := by
  simpa [R_M] using decodeSource_reduce M hTotal x

#print axioms MCore.Real.PNPDiscovery.encode_ntmCNFCircuit_split_at
#print axioms MCore.Real.PNPDiscovery.take_clauseBitOffset
#print axioms MCore.Real.PNPDiscovery.sourceCell_clause_slice
#print axioms MCore.Real.PNPDiscovery.sourceCell_visible_or_hidden
#print axioms MCore.Real.PNPDiscovery.reduction_source_recoverable

end PNPDiscovery
end Real
end MCore
