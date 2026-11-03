import MCore.Real.PNPDiscovery.LayoutDriftFrontier
import MCore.Real.PNPDiscovery.PrefixPressure
import MCore.Real.PNPDiscovery.RightCellInjectivity

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding

/-- Every positive orbit point has source tail starting in false because the
canonical reduction prefix is 100. -/
theorem positiveOrbit_sourceRight0_false
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (n : Nat) :
    sourceRightSymbol
      (orbit M hTotal seed (n + 1)) 0 =
        some false := by
  rcases orbit_succ_fixed_prefix M hTotal seed n with
    ⟨tail, h⟩
  unfold sourceRightSymbol
  rw [h]
  rfl

/-- Canonical left cells are blank at time zero. -/
theorem initialLeftCell_target_none
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat) :
    ((inputTape x).left.getD i M.machine.blank) = none := by
  cases x <;> simp [inputTape, M.blank_none]

/-- At equal clock, when the shorter input's LEFT region ends, the longer
input still has a LEFT cell at that same index. -/
theorem shorterRadius_index_inside_longer
    (x y : BitString)
    (t : Nat)
    (hLen : x.length < y.length) :
    ntmRadius x t < ntmRadius y t := by
  exact ntmRadius_lt_of_length_lt_sameClock x y t hLen

/-- Boundary block on the shorter input: first RIGHT/source cell. -/
def shorterBoundaryRightBlock
    (N : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : NTMCNF :=
  initialRightCellBlock N x t 0

/-- Boundary block on the longer input at the same clause position:
the extra LEFT cell indexed by the shorter radius. -/
def longerBoundaryLeftBlock
    (N : PolyNTMCandidate)
    (x y : BitString)
    (t : Nat) : NTMCNF :=
  ntmSetLeftCell [] N y t 0 (ntmRadius x t) none

/-- In the special t=0 case the variable bases at the boundary coincide,
but the targets still differ: RIGHT[0]=some false versus LEFT=none. -/
theorem boundary_var_eq_when_clock_zero
    (N : PolyNTMCandidate)
    (x y : BitString)
    (a : Option Bool) :
    ntmRightVar N x 0 0 0 a =
      ntmLeftVar N y 0 0 (ntmRadius x 0) a := by
  simp [ntmRightVar, ntmRightBase, ntmLeftVar,
    ntmLeftBase, ntmRadius]
  omega

/-- For positive shorter inputs, the equal-clock LEFT/RIGHT boundary blocks
cannot coincide.  At t=0 targets differ on identical variable IDs; at t>0
the right variable base has an extra t*radius shift and therefore differs. -/
theorem positiveBoundaryBlocks_ne
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (n : Nat)
    (y : BitString)
    (t : Nat) :
    let x := orbit M hTotal seed (n + 1)
    shorterBoundaryRightBlock
        (complementToNTMCandidate M) x t ≠
      longerBoundaryLeftBlock
        (complementToNTMCandidate M) x y t := by
  dsimp
  let N := complementToNTMCandidate M
  let x := orbit M hTotal seed (n + 1)
  have hRight :
      sourceRightSymbol x 0 = some false := by
    exact positiveOrbit_sourceRight0_false M hTotal seed n
  unfold shorterBoundaryRightBlock longerBoundaryLeftBlock
  unfold initialRightCellBlock ntmSetRightCell
  rw [hRight]
  by_cases ht : t = 0
  · subst t
    have hvar :
        ntmRightVar N x 0 0 0 =
          ntmLeftVar N y 0 0 (ntmRadius x 0) := by
      funext a
      exact boundary_var_eq_when_clock_zero N x y a
    rw [hvar]
    intro hEq
    have hTarget :=
      ntmSetSymbolClauses_target_injective
        (ntmLeftVar N y 0 0 (ntmRadius x 0))
        hEq
    simp at hTarget
  · intro hEq
    have hRightLen :=
      encodedSymbolBlock_length_exact
        (ntmRightVar N x t 0 0) (some false)
    have hLeftLen :=
      encodedSymbolBlock_length_exact
        (ntmLeftVar N y t 0 (ntmRadius x t)) none
    have hEnc :
        encodedSymbolBlock
            (ntmRightVar N x t 0 0) (some false) =
          encodedSymbolBlock
            (ntmLeftVar N y t 0 (ntmRadius x t)) none := by
      unfold encodedSymbolBlock
      exact congrArg encodeCNFSpinePrefix hEq
    have hLens := congrArg List.length hEnc
    rw [hRightLen, hLeftLen] at hLens
    simp [ntmRightVar, ntmRightBase, ntmLeftVar,
      ntmLeftBase, ntmRadius] at hLens
    have hr : 0 < ntmRadius x t := ntmRadius_pos x t
    omega

/-- Thus equal-clock length drift necessarily creates a concrete layout
mismatch exactly at the shorter LEFT/RIGHT boundary. -/
theorem equalClock_lengthDrift_has_boundaryMismatch
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (i d : Nat)
    (hClock :
      M.timeBound
          (orbit M hTotal seed (i + 1)).length =
        M.timeBound
          (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length) :
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    let t := M.timeBound x.length
    shorterBoundaryRightBlock
        (complementToNTMCandidate M) x t ≠
      longerBoundaryLeftBlock
        (complementToNTMCandidate M) x y t := by
  dsimp
  exact positiveBoundaryBlocks_ne
    M hTotal seed i
    (orbit M hTotal seed ((i + 1) + (2 * d + 1)))
    (M.timeBound (orbit M hTotal seed (i + 1)).length)

#print axioms MCore.Real.PNPDiscovery.positiveOrbit_sourceRight0_false
#print axioms MCore.Real.PNPDiscovery.boundary_var_eq_when_clock_zero
#print axioms MCore.Real.PNPDiscovery.positiveBoundaryBlocks_ne
#print axioms MCore.Real.PNPDiscovery.equalClock_lengthDrift_has_boundaryMismatch

end PNPDiscovery
end Real
end MCore
