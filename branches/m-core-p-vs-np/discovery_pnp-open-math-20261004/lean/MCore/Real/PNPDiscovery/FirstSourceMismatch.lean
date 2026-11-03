import MCore.Real.PNPDiscovery.LengthSourceCompression
import MCore.Real.PNPDiscovery.SourceBitVisibilityPressure

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof

/-- First concrete source mismatch below a finite retained radius. -/
noncomputable def firstSourceMismatch
    (x y : BitString)
    (r : Nat)
    (H : ∃ j : Nat,
      j < r ∧
      sourceRightSymbol x j ≠ sourceRightSymbol y j) : Nat :=
  Nat.find H

theorem firstSourceMismatch_spec
    (x y : BitString)
    (r : Nat)
    (H : ∃ j : Nat,
      j < r ∧
      sourceRightSymbol x j ≠ sourceRightSymbol y j) :
    firstSourceMismatch x y r H < r ∧
      sourceRightSymbol x (firstSourceMismatch x y r H) ≠
        sourceRightSymbol y (firstSourceMismatch x y r H) := by
  exact Nat.find_spec H

theorem firstSourceMismatch_prefix_aligned
    (x y : BitString)
    (r : Nat)
    (H : ∃ j : Nat,
      j < r ∧
      sourceRightSymbol x j ≠ sourceRightSymbol y j) :
    SourceRightPrefixAligned x y
      (firstSourceMismatch x y r H) := by
  intro i hi
  by_contra hDiff
  have hPi :
      i < r ∧
      sourceRightSymbol x i ≠
        sourceRightSymbol y i := by
    constructor
    · have hj :=
        (firstSourceMismatch_spec x y r H).1
      omega
    · exact hDiff
  have hmin :=
    Nat.find_min' H hi
  exact hmin hPi

/-- A length-aligned terminal-parity-barrier pair yields a complete
SourceMismatchWitness at the first differing source cell. -/
noncomputable def barrierFirstSourceMismatchWitness
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat)
    (hLen :
      (orbit M hTotal seed (i + 1)).length =
        (orbit M hTotal seed ((i + 1) + (2 * d + 1))).length) :
    SourceMismatchWitness M
      (orbit M hTotal seed (i + 1))
      (orbit M hTotal seed ((i + 1) + (2 * d + 1))) := by
  let x := orbit M hTotal seed (i + 1)
  let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
  have hSourceExists :
      ∃ j : Nat,
        j < ntmRadius x (M.timeBound x.length) ∧
        sourceRightSymbol x j ≠ sourceRightSymbol y j := by
    have h :=
      parityBarrier_length_or_source_clean
        M hTotal Hbar seed i d
    rcases h with hL | hS
    · exact False.elim (hL hLen)
    · exact hS
  let j :=
    firstSourceMismatch
      x y
      (ntmRadius x (M.timeBound x.length))
      hSourceExists
  have hj :=
    firstSourceMismatch_spec
      x y
      (ntmRadius x (M.timeBound x.length))
      hSourceExists
  have hPrefix :=
    firstSourceMismatch_prefix_aligned
      x y
      (ntmRadius x (M.timeBound x.length))
      hSourceExists
  refine
    { j := j
      length_eq := hLen
      clock_eq := ?_
      head_eq := ?_
      prefix_eq := ?_
      source_diff := ?_
      in_radius := ?_ }
  · exact clock_eq_of_length_eq M x y hLen
  · dsimp [x, y]
    exact positiveOrbit_sourceHead_eq
      M hTotal seed i (i + (2 * d + 1))
  · exact hPrefix
  · exact hj.2
  · omega

/-- Hence every barrier pair has now only two possibilities:
different lengths, or a canonical first-source-mismatch witness with all
previous source cells aligned. -/
theorem parityBarrier_length_or_firstSourceWitness
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    x.length ≠ y.length ∨
      Nonempty (SourceMismatchWitness M x y) := by
  dsimp
  classical
  let x := orbit M hTotal seed (i + 1)
  let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
  by_cases hLen : x.length = y.length
  · right
    exact ⟨barrierFirstSourceMismatchWitness
      M hTotal Hbar seed i d hLen⟩
  · exact Or.inl hLen

#print axioms MCore.Real.PNPDiscovery.firstSourceMismatch_spec
#print axioms MCore.Real.PNPDiscovery.firstSourceMismatch_prefix_aligned
#print axioms MCore.Real.PNPDiscovery.barrierFirstSourceMismatchWitness
#print axioms MCore.Real.PNPDiscovery.parityBarrier_length_or_firstSourceWitness

end PNPDiscovery
end Real
end MCore
