import MCore.Real.PNPDiscovery.HeadBlockFrontier
import MCore.Real.PNPNTMTableauEncoding

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding
open P02ComplementRunRealization

/-- Tail of the canonical source after the head cell. -/
def sourceTail : BitString → BitString
  | [] => []
  | _ :: bs => bs

@[simp] theorem inputTape_right_eq_sourceTail_map
    (x : BitString) :
    (inputTape x).right = (sourceTail x).map some := by
  cases x <;> rfl

/-- Exact source symbol seen in right-tape cell i at time zero. -/
def sourceRightSymbol
    (x : BitString)
    (i : Nat) : Option Bool :=
  ((inputTape x).right).getD i none

/-- Exact three-clause block used for one source/right cell. -/
def initialRightCellBlock
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat) : NTMCNF :=
  ntmSetRightCell [] M x t 0 i
    (sourceRightSymbol x i)

/-- Right-cell variable identities depend only on source length, clock,
cell index and symbol code; source contents do not enter the variable ID. -/
theorem ntmRightVar_eq_of_length_clock
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t u i : Nat)
    (a : Option Bool)
    (hLen : x.length = y.length)
    (hClock : t = u) :
    ntmRightVar M x t 0 i a =
      ntmRightVar M y u 0 i a := by
  subst u
  exact ntmRightVar_eq_of_length_eq M a hLen

/-- One source-cell block is identical whenever layout parameters and that
single source symbol agree. -/
theorem initialRightCellBlock_eq
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t u i : Nat)
    (hLen : x.length = y.length)
    (hClock : t = u)
    (hSymbol :
      sourceRightSymbol x i =
        sourceRightSymbol y i) :
    initialRightCellBlock M x t i =
      initialRightCellBlock M y u i := by
  subst u
  unfold initialRightCellBlock
  unfold ntmSetRightCell
  unfold sourceRightSymbol at hSymbol
  have hvar :
      (ntmRightVar M x t 0 i) =
        (ntmRightVar M y t 0 i) := by
    funext a
    exact ntmRightVar_eq_of_length_eq M a hLen
  rw [hvar, hSymbol]

/-- If a source-tail index is in range, the time-zero right symbol is exactly
the corresponding source bit. -/
theorem sourceRightSymbol_of_lt
    (b : Bool)
    (bs : BitString)
    (i : Nat)
    (hi : i < bs.length) :
    sourceRightSymbol (b :: bs) i =
      some (bs.getD i false) := by
  unfold sourceRightSymbol
  simp only [inputTape]
  induction bs generalizing i with
  | nil =>
      simp at hi
  | cons c cs ih =>
      cases i with
      | zero =>
          simp [List.getD_cons_zero]
      | succ i =>
          have hi' : i < cs.length := by
            simpa using hi
          simpa [List.getD_cons_succ] using ih i hi'

/-- Past the source tail, the canonical right side is blank. -/
theorem sourceRightSymbol_of_ge
    (b : Bool)
    (bs : BitString)
    (i : Nat)
    (hi : bs.length ≤ i) :
    sourceRightSymbol (b :: bs) i = none := by
  unfold sourceRightSymbol
  simp only [inputTape]
  induction bs generalizing i with
  | nil =>
      simp
  | cons c cs ih =>
      cases i with
      | zero =>
          simp at hi
      | succ i =>
          have hi' : cs.length ≤ i := by
            simpa using hi
          simpa [List.getD_cons_succ] using ih i hi'

/-- Local dependency record for one encoded source cell. -/
structure SourceCellAlignment
    (M : PolyDTMCandidate)
    (x y : BitString)
    (i : Nat) : Prop where
  length_eq : x.length = y.length
  clock_eq :
    M.timeBound x.length = M.timeBound y.length
  symbol_eq :
    sourceRightSymbol x i = sourceRightSymbol y i

/-- Source-cell alignment gives equality of the exact three-clause block. -/
theorem sourceCellAlignment_block_eq
    (M : PolyDTMCandidate)
    (x y : BitString)
    (i : Nat)
    (H : SourceCellAlignment M x y i) :
    initialRightCellBlock
        (complementToNTMCandidate M)
        x (M.timeBound x.length) i =
      initialRightCellBlock
        (complementToNTMCandidate M)
        y (M.timeBound y.length) i := by
  exact initialRightCellBlock_eq
    (complementToNTMCandidate M)
    x y
    (M.timeBound x.length)
    (M.timeBound y.length)
    i
    H.length_eq
    H.clock_eq
    H.symbol_eq

/-- A disagreement in one aligned source-cell block must come from either
layout disagreement or the source symbol itself. -/
theorem rightCell_difference_causes
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t u i : Nat)
    (hDiff :
      initialRightCellBlock M x t i ≠
        initialRightCellBlock M y u i) :
    x.length ≠ y.length ∨
      t ≠ u ∨
      sourceRightSymbol x i ≠ sourceRightSymbol y i := by
  classical
  by_cases hLen : x.length = y.length
  · by_cases hClock : t = u
    · right
      right
      intro hSymbol
      exact hDiff
        (initialRightCellBlock_eq
          M x y t u i hLen hClock hSymbol)
    · exact Or.inr (Or.inl hClock)
  · exact Or.inl hLen

/-- This is the exact local source frontier: after machine/layout parameters
are aligned, the only remaining cause of a right-cell block difference is a
source-symbol difference at that cell. -/
theorem aligned_rightCell_difference_implies_source_difference
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t : Nat)
    (i : Nat)
    (hLen : x.length = y.length)
    (hDiff :
      initialRightCellBlock M x t i ≠
        initialRightCellBlock M y t i) :
    sourceRightSymbol x i ≠ sourceRightSymbol y i := by
  intro hSymbol
  exact hDiff
    (initialRightCellBlock_eq M x y t t i hLen rfl hSymbol)

#print axioms MCore.Real.PNPDiscovery.ntmRightVar_eq_of_length_clock
#print axioms MCore.Real.PNPDiscovery.initialRightCellBlock_eq
#print axioms MCore.Real.PNPDiscovery.sourceRightSymbol_of_lt
#print axioms MCore.Real.PNPDiscovery.rightCell_difference_causes
#print axioms MCore.Real.PNPDiscovery.aligned_rightCell_difference_implies_source_difference

end PNPDiscovery
end Real
end MCore
