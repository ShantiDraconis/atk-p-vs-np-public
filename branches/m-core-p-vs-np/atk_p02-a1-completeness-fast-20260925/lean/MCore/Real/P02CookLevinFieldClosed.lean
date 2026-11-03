import MCore.Real.P02ClockedDiagonalCompiler
import MCore.Real.P02KleeneCookLevinBridge

namespace MCore
namespace Real
namespace P02CookLevinFieldClosed

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02G21G22Attack
open P02KleeneBridge
open P02KleeneCookLevinBridge
open P02ClockedDiagonalCompiler

/-- The pointwise semantic Cook-Levin/rejection equivalence is already
provable for every supplied carrier input.  This theorem does not assert
self-reference and therefore does not reopen the falsified literal route. -/
theorem cook_levin_correct_pointwise
    (M : PolyDTMCandidate)
    (x : BitString) :
    SATTarget (encodeCircuit (semanticDiagonalCircuit M x)) ↔
      ¬ AcceptsAtDeclaredBound M x := by
  simpa [semanticDiagonalBits] using semanticDiagonalBits_flip M x

/-- For any chosen code-to-input carrier, the Cook-Levin field itself can be
filled without an additional hypothesis. -/
theorem cook_levin_correct_for_carrier
    (M : PolyDTMCandidate)
    (selfInput : Nat.Partrec.Code → BitString) :
    ∀ c : Nat.Partrec.Code,
      SATTarget
          (encodeCircuit (semanticDiagonalCircuit M (selfInput c))) ↔
        ¬ AcceptsAtDeclaredBound M (selfInput c) := by
  intro c
  exact cook_levin_correct_pointwise M (selfInput c)

/-
Important firewall:
using semanticDiagonalCircuit for circuitOf makes the SAME-INPUT equation
selfInput c = semanticDiagonalBits M (selfInput c).  Universal existence of
that literal equation is already refuted elsewhere.  Therefore this file
closes only cook_levin_correct as an isolated semantic obligation; the live
route to P02 must use the extensional code compiler, not a universal literal
BitString fixed point.
-/

#print axioms MCore.Real.P02CookLevinFieldClosed.cook_levin_correct_pointwise
#print axioms MCore.Real.P02CookLevinFieldClosed.cook_levin_correct_for_carrier

end P02CookLevinFieldClosed
end Real
end MCore
