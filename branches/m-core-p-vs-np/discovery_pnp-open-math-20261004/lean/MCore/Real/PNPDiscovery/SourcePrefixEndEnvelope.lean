import MCore.Real.PNPDiscovery.SourcePrefixEndExpansion

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding

/-- Candidate-only constant cost of the time-zero state block. -/
def stateEncodingCost
    (M : PolyDTMCandidate) : Nat :=
  (initialStateEncodingPrefix M).length

/-- Explicit upper envelope for one time-zero left-cell encoded block. -/
def leftCellEncodingEnvelope
    (M : PolyNTMCandidate)
    (n t : Nat) : Nat :=
  3 * (ntmLeftBase M (List.replicate n false) t +
    3 * (n + t + 1)) + 48

/-- Explicit upper envelope for one time-zero right-cell encoded block. -/
def rightCellEncodingEnvelope
    (M : PolyNTMCandidate)
    (n t j : Nat) : Nat :=
  3 * (ntmRightBase M (List.replicate n false) t +
    3 * j) + 48

/-- Fully explicit polynomial-style envelope through source cell j.
The machine-dependent state block remains as one candidate constant. -/
def sourcePrefixEndEnvelope
    (D : PolyDTMCandidate)
    (n t j : Nat) : Nat :=
  let M := complementToNTMCandidate D
  let r := n + t + 1
  stateEncodingCost D +
    (3 * ntmHeadBase M t + 48) +
    r * leftCellEncodingEnvelope M n t +
    (j + 1) * rightCellEncodingEnvelope M n t j

/-- Left-base depends only on input length, not source contents. -/
theorem ntmLeftBase_layout
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    ntmLeftBase M x t =
      ntmLeftBase M (List.replicate x.length false) t := by
  simp [ntmLeftBase, ntmRadius]

/-- Right-base likewise depends only on length. -/
theorem ntmRightBase_layout
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    ntmRightBase M x t =
      ntmRightBase M (List.replicate x.length false) t := by
  simp [ntmRightBase, ntmLeftBase, ntmRadius]

/-- Every left cell below the retained radius is bounded by the common
length/clock envelope. -/
theorem encoded_leftCell_le_envelope
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t)
    (target : Option Bool) :
    (encodedSymbolBlock
      (ntmLeftVar M x t 0 i)
      target).length ≤
      leftCellEncodingEnvelope M x.length t := by
  rw [encoded_initialLeftCell_length]
  unfold leftCellEncodingEnvelope
  rw [ntmLeftBase_layout M x t]
  simp
  have hir :
      i ≤ x.length + t := by
    simp [ntmRadius] at hi
    omega
  omega

/-- Every right cell among 0..j is bounded by the j-cell envelope. -/
theorem encoded_rightCell_le_envelope
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i j : Nat)
    (hij : i ≤ j)
    (target : Option Bool) :
    (encodedSymbolBlock
      (ntmRightVar M x t 0 i)
      target).length ≤
      rightCellEncodingEnvelope M x.length t j := by
  rw [encoded_initialRightCell_length]
  unfold rightCellEncodingEnvelope
  rw [ntmRightBase_layout M x t]
  simp
  omega

/-- Generic bound for a range-flatMap when every block has bounded encoded
spine length. -/
theorem encodeSpine_flatMap_range_le
    (f : Nat → NTMCNF)
    (B : Nat)
    (k : Nat)
    (hB : ∀ i, i < k →
      (encodeCNFSpinePrefix (f i)).length ≤ B) :
    (encodeCNFSpinePrefix
      ((List.range k).flatMap f)).length ≤
        k * B := by
  induction k with
  | zero =>
      simp [encodeCNFSpinePrefix]
  | succ k ih =>
      rw [List.range_succ, List.flatMap_append,
        encodeCNFSpinePrefix_append]
      simp only [List.flatMap_singleton, List.length_append]
      have hk :
          (encodeCNFSpinePrefix (f k)).length ≤ B :=
        hB k (Nat.lt_succ_self k)
      have hp :
          (encodeCNFSpinePrefix
            ((List.range k).flatMap f)).length ≤ k * B := by
        apply ih
        intro i hi
        exact hB i (Nat.lt.step hi)
      omega

/-- Exact head-block encoded-spine length. -/
theorem encodeSpine_initialHeadBlock_length
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    (encodeCNFSpinePrefix
      (initialHeadBlock M x t)).length =
      3 * ntmHeadBase M t + 48 := by
  unfold initialHeadBlock
  change
    (encodedSymbolBlock
      (ntmHeadVar M t 0)
      (sourceHeadSymbol x)).length =
      3 * ntmHeadBase M t + 48
  exact encoded_initialHeadBlock_length
    M t (sourceHeadSymbol x)

/-- Left-block encoded-spine bound. -/
theorem encodeSpine_initialLeftBlock_le
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    (encodeCNFSpinePrefix
      (initialLeftBlock M x t)).length ≤
      ntmRadius x t *
        leftCellEncodingEnvelope M x.length t := by
  unfold initialLeftBlock
  apply encodeSpine_flatMap_range_le
  intro i hi
  unfold ntmSetLeftCell
  change
    (encodedSymbolBlock
      (ntmLeftVar M x t 0 i)
      ((inputTape x).left.getD i M.machine.blank)).length ≤
      leftCellEncodingEnvelope M x.length t
  exact encoded_leftCell_le_envelope
    M x t i hi _

/-- First j+1 right/source cells encoded-spine bound. -/
theorem encodeSpine_firstKRightBlocks_le
    (M : PolyNTMCandidate)
    (x : BitString)
    (t j : Nat) :
    (encodeCNFSpinePrefix
      (firstKRightBlocks M x t (j + 1))).length ≤
      (j + 1) * rightCellEncodingEnvelope M x.length t j := by
  unfold firstKRightBlocks
  apply encodeSpine_flatMap_range_le
  intro i hi
  have hij : i ≤ j := by omega
  unfold initialRightCellBlock ntmSetRightCell
  change
    (encodedSymbolBlock
      (ntmRightVar M x t 0 i)
      (sourceRightSymbol x i)).length ≤
      rightCellEncodingEnvelope M x.length t j
  exact encoded_rightCell_le_envelope
    M x t i j hij _

/-- Core expansion theorem: sourcePrefixBitEnd is bounded by an explicit
polynomial expression in input length, clock, source index and machine data. -/
theorem sourcePrefixBitEnd_le_envelope
    (D : PolyDTMCandidate)
    (x : BitString)
    (t j : Nat)
    (hj : j + 1 ≤ ntmRadius x t) :
    sourcePrefixBitEnd
        (complementToNTMCandidate D)
        x t (j + 1) ≤
      sourcePrefixEndEnvelope D x.length t j := by
  let M := complementToNTMCandidate D
  unfold sourcePrefixBitEnd tableauClauseBitOffset clauseBitOffset
  rw [boundedExec_take_sourcePrefix M x t (j + 1) hj]
  unfold sourcePrefixClauses
  repeat rw [encodeCNFSpinePrefix_append]
  simp only [List.length_append]
  have hState :
      (encodeCNFSpinePrefix
        (ntmSetStateClauses [] M t 0 M.machine.initial)).length =
        stateEncodingCost D := by
    unfold stateEncodingCost initialStateEncodingPrefix
    have hs :=
      initialStateClauses_clock_independent M t 0
    rw [hs]
  have hHead :=
    encodeSpine_initialHeadBlock_length M x t
  have hLeft :=
    encodeSpine_initialLeftBlock_le M x t
  have hRight :=
    encodeSpine_firstKRightBlocks_le M x t j
  unfold sourcePrefixEndEnvelope
  dsimp
  rw [hState, hHead]
  have hr : ntmRadius x t = x.length + t + 1 := by
    rfl
  rw [hr] at hLeft
  omega

#print axioms MCore.Real.PNPDiscovery.encoded_leftCell_le_envelope
#print axioms MCore.Real.PNPDiscovery.encoded_rightCell_le_envelope
#print axioms MCore.Real.PNPDiscovery.encodeSpine_flatMap_range_le
#print axioms MCore.Real.PNPDiscovery.sourcePrefixBitEnd_le_envelope

end PNPDiscovery
end Real
end MCore
