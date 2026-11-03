import Mathlib
import MCore.Real.P02UniversalFailureAlgebra
import MCore.Real.OpenMathCore.SelfQuotation

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open P02DiagonalFrontier
open P02UniversalFailureAlgebra

structure BoundedUniversalSimulator where
  simulate :
    PolyDTMCandidate → BitString → Bool
  exact :
    ∀ M x,
      simulate M x = true ↔
        AcceptsAtDeclaredBound M x
  total_on_declared_clock :
    ∀ M, DeclaredClockTotal M →
      ∀ x, simulate M x = true ∨ simulate M x = false

/-- Concrete bounded simulator for the repository's declared-clock semantics.
It simply evaluates the already-total fuelled machine execution and observes
the candidate's accepting predicate. -/
def declaredClockSimulator : BoundedUniversalSimulator where
  simulate := fun M x =>
    P02ClockedDiagonalCompiler.declaredAcceptBit M x
  exact := by
    intro M x
    exact P02ClockedDiagonalCompiler.declaredAcceptBit_true_iff M x
  total_on_declared_clock := by
    intro M _hTotal x
    cases h :
        P02ClockedDiagonalCompiler.declaredAcceptBit M x <;>
      simp [h]

theorem boundedUniversalSimulator_nonempty :
    Nonempty BoundedUniversalSimulator :=
  ⟨declaredClockSimulator⟩

end MCore.Real.OpenMathCore
