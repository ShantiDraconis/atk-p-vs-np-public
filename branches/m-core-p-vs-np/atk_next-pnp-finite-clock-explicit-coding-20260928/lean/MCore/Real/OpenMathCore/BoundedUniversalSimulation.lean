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

end MCore.Real.OpenMathCore
