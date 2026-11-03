import MCore.Real.PNPDiscovery.SourceOffsetVisibilityLaw
import MCore.Real.PNPDiscovery.SourcePrefixEndExpansion

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding

/-- Simple candidate/layout-dependent lower envelope for the bit offset of
source cell j.  Unary variable encoding makes every earlier symbol block cost
at least its base contribution. -/
def sourceCellOffsetLowerEnvelope
    (D : PolyDTMCandidate)
    (n t j : Nat) : Nat :=
  let M := complementToNTMCandidate D
  let r := n + t + 1
  stateEncodingCost D +
    (3 * ntmHeadBase M t + 48) +
    r * (3 * ntmLeftBase M (List.replicate n false) t + 48) +
    j * (3 * ntmRightBase M (List.replicate n false) t + 48)

/-- Every encoded left cell costs at least the base term. -/
theorem encoded_leftCell_ge_base
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (target : Option Bool) :
    3 * ntmLeftBase M x t + 48 ≤
      (encodedSymbolBlock
        (ntmLeftVar M x t 0 i)
        target).length := by
  rw [encoded_initialLeftCell_length]
  omega

/-- Every encoded right cell costs at least the right-base term. -/
theorem encoded_rightCell_ge_base
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (target : Option Bool) :
    3 * ntmRightBase M x t + 48 ≤
      (encodedSymbolBlock
        (ntmRightVar M x t 0 i)
        target).length := by
  rw [encoded_initialRightCell_length]
  omega

/-- Generic lower bound for encoding a range-flatMap when each block has a
uniform encoded-spine lower bound. -/
theorem mul_le_encodeSpine_flatMap_range
    (f : Nat → NTMCNF)
    (B k : Nat)
    (hB : ∀ i, i < k →
      B ≤ (encodeCNFSpinePrefix (f i)).length) :
    k * B ≤
      (encodeCNFSpinePrefix
        ((List.range k).flatMap f)).length := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, List.flatMap_append,
        encodeCNFSpinePrefix_append]
      simp only [List.flatMap_singleton, List.length_append]
      have hk := hB k (Nat.lt_succ_self k)
      have hp : k * B ≤
          (encodeCNFSpinePrefix
            ((List.range k).flatMap f)).length := by
        apply ih
        intro i hi
        exact hB i (Nat.lt.step hi)
      omega

/-- Lower bound for the whole canonical left region. -/
theorem encodeSpine_initialLeftBlock_ge
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    ntmRadius x t *
        (3 * ntmLeftBase M x t + 48) ≤
      (encodeCNFSpinePrefix
        (initialLeftBlock M x t)).length := by
  unfold initialLeftBlock
  apply mul_le_encodeSpine_flatMap_range
  intro i hi
  unfold ntmSetLeftCell
  change
    3 * ntmLeftBase M x t + 48 ≤
      (encodedSymbolBlock
        (ntmLeftVar M x t 0 i)
        ((inputTape x).left.getD i M.machine.blank)).length
  exact encoded_leftCell_ge_base M x t i _

/-- Lower bound for the first j right/source blocks. -/
theorem encodeSpine_firstKRightBlocks_ge
    (M : PolyNTMCandidate)
    (x : BitString)
    (t j : Nat) :
    j * (3 * ntmRightBase M x t + 48) ≤
      (encodeCNFSpinePrefix
        (firstKRightBlocks M x t j)).length := by
  unfold firstKRightBlocks
  apply mul_le_encodeSpine_flatMap_range
  intro i hi
  unfold initialRightCellBlock ntmSetRightCell
  change
    3 * ntmRightBase M x t + 48 ≤
      (encodedSymbolBlock
        (ntmRightVar M x t 0 i)
        (sourceRightSymbol x i)).length
  exact encoded_rightCell_ge_base M x t i _

/-- Explicit lower bound for sourceCellBitOffset(j). -/
theorem sourceCellOffsetLowerEnvelope_le
    (D : PolyDTMCandidate)
    (x : BitString)
    (t j : Nat)
    (hj : j ≤ ntmRadius x t) :
    sourceCellOffsetLowerEnvelope D x.length t j ≤
      sourceCellBitOffset
        (complementToNTMCandidate D)
        x t j := by
  let M := complementToNTMCandidate D
  rw [sourceCellBitOffset_eq_prefix_length M x t j hj]
  unfold sourcePrefixClauses
  repeat rw [encodeCNFSpinePrefix_append]
  simp only [List.length_append]
  have hState :
      (encodeCNFSpinePrefix
        (ntmSetStateClauses [] M t 0 M.machine.initial)).length =
        stateEncodingCost D := by
    unfold stateEncodingCost initialStateEncodingPrefix
    rw [initialStateClauses_clock_independent M t 0]
  have hHead :=
    encodeSpine_initialHeadBlock_length M x t
  have hLeft :=
    encodeSpine_initialLeftBlock_ge M x t
  have hRight :=
    encodeSpine_firstKRightBlocks_ge M x t j
  unfold sourceCellOffsetLowerEnvelope
  dsimp
  rw [hState, hHead]
  rw [ntmLeftBase_layout M x t] at hLeft
  rw [ntmRightBase_layout M x t] at hRight
  have hr : ntmRadius x t = x.length + t + 1 := rfl
  rw [hr] at hLeft
  omega

/-- The equal-length barrier branch now implies a completely explicit
necessary inequality between a Cook--Levin source-layout lower envelope and
the candidate's successor-clock upper envelope. -/
theorem barrier_equalLength_explicit_growth_constraint
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat)
    (hLen :
      (orbit M hTotal seed (i + 1)).length =
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length) :
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    let W :=
      barrierFirstSourceMismatchWitness
        M hTotal Hbar seed i d hLen
    sourceCellOffsetLowerEnvelope
        M x.length (M.timeBound x.length) W.j <
      successorSharedConeEnvelope M x y := by
  dsimp
  let x := orbit M hTotal seed (i + 1)
  let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
  let W :=
    barrierFirstSourceMismatchWitness
      M hTotal Hbar seed i d hLen
  have hLow :
      sourceCellOffsetLowerEnvelope
          M x.length (M.timeBound x.length) W.j ≤
        sourceCellBitOffset
          (complementToNTMCandidate M)
          x (M.timeBound x.length) W.j := by
    apply sourceCellOffsetLowerEnvelope_le
    exact Nat.le_of_lt W.in_radius
  have hHigh :=
    barrier_equalLength_sourceOffset_lt_clockEnvelope
      M hTotal Hbar seed i d hLen
  omega

#print axioms MCore.Real.PNPDiscovery.encoded_leftCell_ge_base
#print axioms MCore.Real.PNPDiscovery.mul_le_encodeSpine_flatMap_range
#print axioms MCore.Real.PNPDiscovery.sourceCellOffsetLowerEnvelope_le
#print axioms MCore.Real.PNPDiscovery.barrier_equalLength_explicit_growth_constraint

end PNPDiscovery
end Real
end MCore
