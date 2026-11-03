import MCore.Real.PNPDiscovery.FullSourceDichotomy
import MCore.Real.PNPDiscovery.PrefixPressure

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof

/-- Equal input length gives equal declared clock definitionally. -/
theorem clock_eq_of_length_eq
    (M : PolyDTMCandidate)
    (x y : BitString)
    (hLen : x.length = y.length) :
    M.timeBound x.length = M.timeBound y.length := by
  rw [hLen]

/-- Every positive orbit point has first source/head symbol true because the
real reduction encoding begins with the fixed bit 1 of the 100 tag. -/
theorem positiveOrbit_sourceHead_true
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (n : Nat) :
    sourceHeadSymbol (orbit M hTotal seed (n + 1)) =
      some true := by
  rcases orbit_succ_fixed_prefix M hTotal seed n with
    ⟨tail, h⟩
  unfold sourceHeadSymbol
  rw [h]
  rfl

/-- Hence any two positive orbit points have identical source-head symbols. -/
theorem positiveOrbit_sourceHead_eq
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (i j : Nat) :
    sourceHeadSymbol (orbit M hTotal seed (i + 1)) =
      sourceHeadSymbol (orbit M hTotal seed (j + 1)) := by
  rw [positiveOrbit_sourceHead_true M hTotal seed i]
  rw [positiveOrbit_sourceHead_true M hTotal seed j]

/-- Clean proof of the compressed dichotomy without relying on nested branch
information from the older theorem. -/
theorem parityBarrier_length_or_source_clean
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    x.length ≠ y.length ∨
    ∃ j : Nat,
      j < ntmRadius x (M.timeBound x.length) ∧
      sourceRightSymbol x j ≠ sourceRightSymbol y j := by
  dsimp
  classical
  let x := orbit M hTotal seed (i + 1)
  let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
  by_cases hLen : x.length = y.length
  · right
    have hClock :
        M.timeBound x.length = M.timeBound y.length :=
      clock_eq_of_length_eq M x y hLen
    have hHead :
        sourceHeadSymbol x = sourceHeadSymbol y := by
      dsimp [x, y]
      exact positiveOrbit_sourceHead_eq
        M hTotal seed i (i + (2 * d + 1))
    have hOld :=
      parityBarrier_source_break_dichotomy
        M hTotal Hbar seed i d
    rcases hOld with hL | hC | hH | hS
    · exact False.elim (hL hLen)
    · exact False.elim (hC hClock)
    · exact False.elim (hH hHead)
    · exact hS
  · exact Or.inl hLen

#print axioms MCore.Real.PNPDiscovery.clock_eq_of_length_eq
#print axioms MCore.Real.PNPDiscovery.positiveOrbit_sourceHead_true
#print axioms MCore.Real.PNPDiscovery.positiveOrbit_sourceHead_eq
#print axioms MCore.Real.PNPDiscovery.parityBarrier_length_or_source_clean

end PNPDiscovery
end Real
end MCore
