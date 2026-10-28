import MCore.Real.P02FinalProofProducer
import MCore.Real.P02CookLevinFromBoundedExec
import MCore.Real.P02TableauCompletenessClose

namespace MCore
namespace Real
namespace P02SameInputOnlyFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02G21G22Attack
open P02KleeneBridge
open P02KleeneCookLevinBridge
open P02CookLevinFromBoundedExec
open P02TableauCompletenessClose
open P02FinalProofProducer

/-- After the bounded-execution/Cook-Levin proof is closed, the only uniform
semantic construction still required is a computable fixed-point carrier with
the exact same-input transport.  Cook-Levin correctness is derived, not stored
as an assumption. -/
structure SameInputCore where
  compiler : ∀ M : PolyDTMCandidate, EffectiveDiagonalCompiler M
  transport :
    ∀ M : PolyDTMCandidate,
      SameInputTransport M (compiler M)

/-- The already-kernelized tableau theorem supplies all Cook-Levin semantic
correctness fields. -/
def SameInputCore.toProducer
    (S : SameInputCore) :
    P02FinalProofProducer.Producer where
  compiler := S.compiler
  carrier := fun M =>
    { circuitOf := fun c =>
        rejectCircuit M ((S.transport M).selfInput c)
      selfInput := (S.transport M).selfInput }
  cook_levin_correct := by
    intro M c
    exact rejectCircuit_cook_levin_correct
      boundedExecCorrectness_closed M ((S.transport M).selfInput c)
  same_input_of_fixed := by
    intro M c hfixed
    exact (S.transport M).same_input_of_fixed c hfixed

/-- No further mathematical producer is required after SameInputCore. -/
theorem SameInputCore.toG21
    (S : SameInputCore) :
    G21Pointwise :=
  S.toProducer.toG21

theorem SameInputCore.toP02Target
    (S : SameInputCore) :
    P02TerminalFrontier.P02Target :=
  S.toProducer.toP02Target

/-- Exact remaining G21 construction target after importing the completed
bounded-execution tableau and Mathlib's Kleene theorem. -/
def SameInputCoreGap : Prop :=
  Nonempty SameInputCore

theorem sameInputCoreGap_closes_G21
    (h : SameInputCoreGap) :
    G21Pointwise := by
  rcases h with ⟨S⟩
  exact S.toG21

#print axioms MCore.Real.P02SameInputOnlyFrontier.SameInputCore.toProducer
#print axioms MCore.Real.P02SameInputOnlyFrontier.SameInputCore.toG21
#print axioms MCore.Real.P02SameInputOnlyFrontier.sameInputCoreGap_closes_G21

end P02SameInputOnlyFrontier
end Real
end MCore
