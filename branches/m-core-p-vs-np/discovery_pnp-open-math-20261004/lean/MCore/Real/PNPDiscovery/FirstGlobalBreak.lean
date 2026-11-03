import MCore.Real.PNPDiscovery.FirstSourceMismatch
import MCore.Real.PNPDiscovery.OrbitLevelAlignmentCorrection

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02TableauDynamics

/-- Unequal finite bitstrings differ at some finite prefix length. -/
theorem unequalBitstrings_have_prefixBreak
    (a b : BitString)
    (hab : a ≠ b) :
    ∃ k : Nat, a.take k ≠ b.take k := by
  refine ⟨Nat.max a.length b.length + 1, ?_⟩
  intro h
  have ha :
      a.take (Nat.max a.length b.length + 1) = a := by
    apply List.take_eq_self.mpr
    omega
  have hb :
      b.take (Nat.max a.length b.length + 1) = b := by
    apply List.take_eq_self.mpr
    omega
  exact hab (by simpa [ha, hb] using h)

/-- First prefix length at which two unequal bitstrings become distinguishable. -/
noncomputable def firstPrefixBreak
    (a b : BitString)
    (hab : a ≠ b) : Nat :=
  Nat.find (unequalBitstrings_have_prefixBreak a b hab)

theorem firstPrefixBreak_spec
    (a b : BitString)
    (hab : a ≠ b) :
    a.take (firstPrefixBreak a b hab) ≠
      b.take (firstPrefixBreak a b hab) := by
  exact Nat.find_spec (unequalBitstrings_have_prefixBreak a b hab)

theorem firstPrefixBreak_before_equal
    (a b : BitString)
    (hab : a ≠ b)
    (k : Nat)
    (hk : k < firstPrefixBreak a b hab) :
    a.take k = b.take k := by
  by_contra h
  have hmin :=
    Nat.find_min'
      (unequalBitstrings_have_prefixBreak a b hab)
      hk
  exact hmin h

theorem firstPrefixBreak_positive
    (a b : BitString)
    (hab : a ≠ b) :
    0 < firstPrefixBreak a b hab := by
  by_contra h
  have hz : firstPrefixBreak a b hab = 0 := by omega
  have hs := firstPrefixBreak_spec a b hab
  simpa [hz] using hs

/-- Terminal parity barrier forces every relevant successor pair to be unequal
as literal bitstrings. -/
theorem barrier_successors_ne
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    R_M M hTotal (orbit M hTotal seed (i + 1)) ≠
      R_M M hTotal
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))) := by
  intro hEq
  have hState :
      terminalState M
          (orbit M hTotal seed ((i + 1) + 1)) =
        terminalState M
          (orbit M hTotal seed
            (((i + 1) + (2 * d + 1)) + 1)) := by
    simpa [orbit, reductionMap_eq_R_M,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (terminalState M) hEq
  have hBarrier :=
    Hbar seed (i + 1) d
  exact hBarrier (by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hState)

/-- Canonical first global break of the two successor encodings. -/
noncomputable def successorFirstPrefixBreak
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) : Nat :=
  firstPrefixBreak
    (R_M M hTotal (orbit M hTotal seed (i + 1)))
    (R_M M hTotal
      (orbit M hTotal seed ((i + 1) + (2 * d + 1))))
    (barrier_successors_ne M hTotal Hbar seed i d)

/-- Key compression:
under TerminalParityBarrier the first global successor-prefix break must occur
at or before the successor shared read cone.  If it were later, the full
shared prefix would be equal and locality would force equal terminal states. -/
theorem barrier_firstGlobalBreak_visible
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    successorFirstPrefixBreak M hTotal Hbar seed i d ≤
      SuccessorSharedReadConePrefix M hTotal
        (orbit M hTotal seed (i + 1))
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))) := by
  let x := orbit M hTotal seed (i + 1)
  let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
  let rx := R_M M hTotal x
  let ry := R_M M hTotal y
  let hne : rx ≠ ry := by
    exact barrier_successors_ne M hTotal Hbar seed i d
  let k := firstPrefixBreak rx ry hne
  by_contra hNot
  have hConeLt :
      SuccessorSharedReadConePrefix M hTotal x y < k := by
    simpa [successorFirstPrefixBreak, x, y, rx, ry, hne, k] using
      (Nat.lt_of_not_ge hNot)
  have hPrefix :
      rx.take (SuccessorSharedReadConePrefix M hTotal x y) =
        ry.take (SuccessorSharedReadConePrefix M hTotal x y) := by
    exact firstPrefixBreak_before_equal
      rx ry hne
      (SuccessorSharedReadConePrefix M hTotal x y)
      hConeLt
  have hState :
      terminalState M rx = terminalState M ry := by
    exact successorDifferencesHidden_closes_terminalState
      M hTotal x y hPrefix
  have hBarrier := Hbar seed (i + 2) d
  apply hBarrier
  simpa [x, y, rx, ry, orbit, reductionMap_eq_R_M,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hState

#print axioms MCore.Real.PNPDiscovery.unequalBitstrings_have_prefixBreak
#print axioms MCore.Real.PNPDiscovery.firstPrefixBreak_before_equal
#print axioms MCore.Real.PNPDiscovery.barrier_successors_ne
#print axioms MCore.Real.PNPDiscovery.barrier_firstGlobalBreak_visible

end PNPDiscovery
end Real
end MCore
