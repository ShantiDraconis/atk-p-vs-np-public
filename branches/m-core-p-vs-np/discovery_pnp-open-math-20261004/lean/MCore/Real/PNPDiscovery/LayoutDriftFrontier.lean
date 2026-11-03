import MCore.Real.PNPDiscovery.StrictLengthGrowth
import MCore.Real.PNPDiscovery.SourcePrefixEndExpansion
import MCore.Real.PNPDiscovery.EncodingSpine

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding

/-- Head-base is strictly monotone in the declared clock because
ntmStateCount = stateCount+1 is positive. -/
theorem ntmHeadBase_strict_mono
    (M : PolyNTMCandidate)
    {t u : Nat}
    (htu : t < u) :
    ntmHeadBase M t < ntmHeadBase M u := by
  unfold ntmHeadBase ntmStateSlots ntmStateCount
  have hs : 0 < M.stateCount + 1 := by omega
  nlinarith

/-- Therefore different clocks give different encoded head-block lengths. -/
theorem encodedHeadBlock_length_ne_of_clock_ne
    (M : PolyNTMCandidate)
    (t u : Nat)
    (a : Option Bool)
    (htu : t ≠ u) :
    (encodedSymbolBlock (ntmHeadVar M t 0) a).length ≠
      (encodedSymbolBlock (ntmHeadVar M u 0) a).length := by
  rw [encoded_initialHeadBlock_length M t a]
  rw [encoded_initialHeadBlock_length M u a]
  unfold ntmHeadBase ntmStateSlots ntmStateCount
  intro h
  have hs : 0 < M.stateCount + 1 := by omega
  apply htu
  nlinarith

/-- With equal clock, the time-zero head and each common left cell are
definitionally layout-identical for any two positive reduction outputs. -/
theorem equalClock_commonLeftCell_eq
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t : Nat)
    (i : Nat) :
    initialLeftCellBlock M x t i =
      initialLeftCellBlock M y t i := by
  unfold initialLeftCellBlock
  unfold ntmSetLeftCell
  have hvar :
      ntmLeftVar M x t 0 i =
        ntmLeftVar M y t 0 i := by
    funext a
    simp [ntmLeftVar, ntmLeftBase]
  rw [hvar]
  cases x <;> cases y <;> simp [inputTape]

/-- If lengths differ but clocks agree, retained radii differ by exactly the
same length ordering. -/
theorem ntmRadius_lt_of_length_lt_sameClock
    (x y : BitString)
    (t : Nat)
    (hxy : x.length < y.length) :
    ntmRadius x t < ntmRadius y t := by
  simp [ntmRadius]
  omega

/-- Complete structural drift dichotomy for two inputs of different length:
either their clocks differ (head-layout drift), or clocks agree and their
retained left-region lengths differ. -/
inductive LayoutDriftKind
  | headClock
  | leftRadius
  deriving Repr, DecidableEq

def layoutDriftKind
    (M : PolyDTMCandidate)
    (x y : BitString)
    (hxy : x.length ≠ y.length) : LayoutDriftKind :=
  if M.timeBound x.length = M.timeBound y.length
  then .leftRadius
  else .headClock

theorem layoutDrift_cases
    (M : PolyDTMCandidate)
    (x y : BitString)
    (hxy : x.length ≠ y.length) :
    (layoutDriftKind M x y hxy = .headClock ∧
      M.timeBound x.length ≠ M.timeBound y.length) ∨
    (layoutDriftKind M x y hxy = .leftRadius ∧
      M.timeBound x.length = M.timeBound y.length) := by
  unfold layoutDriftKind
  by_cases hClock :
      M.timeBound x.length = M.timeBound y.length
  · right
    simp [hClock]
  · left
    simp [hClock]

/-- On the concrete positive orbit, length drift is universal. -/
theorem positiveOddPair_layoutDrift
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (i d : Nat) :
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    x.length < y.length := by
  dsimp
  apply orbit_length_strict_mono
  omega

#print axioms MCore.Real.PNPDiscovery.ntmHeadBase_strict_mono
#print axioms MCore.Real.PNPDiscovery.encodedHeadBlock_length_ne_of_clock_ne
#print axioms MCore.Real.PNPDiscovery.equalClock_commonLeftCell_eq
#print axioms MCore.Real.PNPDiscovery.positiveOddPair_layoutDrift

end PNPDiscovery
end Real
end MCore
