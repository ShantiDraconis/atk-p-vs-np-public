import Mathlib
import MCore.Real.OpenMathCore.BoundedUniversalSimulation
import MCore.Real.P02ClockedDiagonalCompiler

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02ClockedDiagonalCompiler

structure SATCircuitCompiler where
  compile :
    PolyDTMCandidate → BitString → CircuitK1.Circuit
  compiledBits :
    PolyDTMCandidate → BitString → BitString
  compiledBits_eq :
    ∀ M x, compiledBits M x = encodeCircuit (compile M x)
  valid :
    ∀ M x, CanonicalSATValid (compiledBits M x)
  negates_candidate :
    ∀ M x,
      SATBits circuitBitEncoding (compiledBits M x) ↔
        ¬ AcceptsAtDeclaredBound M x

def clockedSATCompiler : SATCircuitCompiler where
  compile := semanticDiagonalCircuit
  compiledBits := semanticDiagonalBits
  compiledBits_eq := by intro M x; rfl
  valid := semanticDiagonalBits_valid
  negates_candidate := semanticDiagonalBits_flip

end MCore.Real.OpenMathCore
