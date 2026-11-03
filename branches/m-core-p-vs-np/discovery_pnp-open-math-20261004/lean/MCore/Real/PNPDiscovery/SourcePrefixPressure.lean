import MCore.Real.PNPDiscovery.BitRegionMap
import MCore.Real.PNPDiscovery.RightCellInjectivity

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding
open SourceRecovery

/-- First k right/source cell blocks. -/
def firstKRightBlocks
    (M : PolyNTMCandidate)
    (x : BitString)
    (t k : Nat) : NTMCNF :=
  (List.range k).flatMap fun i =>
    initialRightCellBlock M x t i

/-- Clause boundary immediately after the first k right/source cells. -/
def sourcePrefixClauseEnd
    (M : PolyNTMCandidate)
    (x : BitString)
    (t k : Nat) : Nat :=
  rightBlockOffset M x.length t + 3 * k

/-- Encoded-bit boundary immediately after first k source/right cells. -/
def sourcePrefixBitEnd
    (M : PolyNTMCandidate)
    (x : BitString)
    (t k : Nat) : Nat :=
  tableauClauseBitOffset M x t
    (sourcePrefixClauseEnd M x t k)

/-- Alignment payload sufficient to make the first k source cells identical. -/
structure SourcePrefixLayoutAlignment
    (M : PolyDTMCandidate)
    (x y : BitString)
    (k : Nat) : Prop where
  length_eq : x.length = y.length
  clock_eq :
    M.timeBound x.length = M.timeBound y.length
  head_eq :
    sourceHeadSymbol x = sourceHeadSymbol y
  source_eq :
    SourceRightPrefixAligned x y k
  within_radius :
    k ≤ ntmRadius x (M.timeBound x.length)

/-- At clause level, aligned layout and first k source symbols force equality
of all k right/source blocks. -/
theorem firstKRightBlocks_eq
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t k : Nat)
    (hLen : x.length = y.length)
    (hSource : SourceRightPrefixAligned x y k) :
    firstKRightBlocks M x t k =
      firstKRightBlocks M y t k := by
  unfold firstKRightBlocks
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hPrev :
          SourceRightPrefixAligned x y k :=
        sourceRightPrefixAligned_mono x y (Nat.le_succ k) hSource
      have hCell :
          initialRightCellBlock M x t k =
            initialRightCellBlock M y t k :=
        initialRightCellBlock_eq
          M x y t t k hLen rfl
          (hSource k (Nat.lt_succ_self k))
      simpa [List.range_succ, hCell] using ih hPrev

/-- New arithmetic frontier: every additional aligned source cell extends the
candidate-independent/equal prefix to sourcePrefixBitEnd. -/
def SourcePrefixCoverageGap : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (k : Nat),
    SourcePrefixLayoutAlignment M x y k →
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let boundary := sourcePrefixBitEnd N x tx k
    (R_M M hTotal x).take boundary =
      (R_M M hTotal y).take boundary

/-- Once SourcePrefixCoverageGap is discharged definitionally from the encoding,
a terminal parity barrier must place the shared cone strictly beyond every
aligned source prefix. -/
theorem sourcePrefixCoverage_pressures_barrier
    (Hcov : SourcePrefixCoverageGap)
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d k : Nat)
    (A :
      SourcePrefixLayoutAlignment M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1)))
        k) :
    sourcePrefixBitEnd
        (complementToNTMCandidate M)
        (orbit M hTotal seed (i + 1))
        (M.timeBound
          (orbit M hTotal seed (i + 1)).length)
        k <
      SharedReadConePrefix M
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))) := by
  let x := orbit M hTotal seed (i + 1)
  let y :=
    orbit M hTotal seed ((i + 1) + (2 * d + 1))
  let boundary :=
    sourcePrefixBitEnd
      (complementToNTMCandidate M)
      x (M.timeBound x.length) k
  have hPrefix :
      (R_M M hTotal x).take boundary =
        (R_M M hTotal y).take boundary := by
    exact Hcov M hTotal x y k A
  by_contra hNot
  have hCone :
      SharedReadConePrefix M x y ≤ boundary := by
    omega
  have hEq := congrArg
    (fun bs : BitString =>
      bs.take (SharedReadConePrefix M x y))
    hPrefix
  have hShared :
      x.take (SharedReadConePrefix M x y) =
        y.take (SharedReadConePrefix M x y) := by
    change
      (orbit M hTotal seed (i + 1)).take
          (SharedReadConePrefix M x y) =
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))).take
          (SharedReadConePrefix M x y)
    simpa [x, y, boundary, List.take_take,
      Nat.min_eq_left hCone] using hEq
  exact (parityBarrier_forces_sharedCone_difference
    M hTotal Hbar seed (i + 1) d) hShared

#print axioms MCore.Real.PNPDiscovery.firstKRightBlocks_eq
#print axioms MCore.Real.PNPDiscovery.sourcePrefixCoverage_pressures_barrier

end PNPDiscovery
end Real
end MCore
