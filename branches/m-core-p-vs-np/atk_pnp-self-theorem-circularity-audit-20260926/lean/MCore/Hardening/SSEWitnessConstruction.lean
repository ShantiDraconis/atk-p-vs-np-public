import MCore.Real.P02FinalProofProducer
import MCore.Real.P02CookLevinFromBoundedExec
import MCore.Real.P02TableauCompletenessClose
import MCore.Hardening.SSEStatementFrozen

namespace MCore.Hardening.SSEWitnessConstruction

open MCore.Real
open MCore.Real.P02KleeneBridge
open MCore.Real.P02KleeneCookLevinBridge
open MCore.Real.P02FinalProofProducer
open MCore.Real.P02CookLevinFromBoundedExec

/-- Hardened decomposition of the live SSE route.
No inhabitant is asserted. Each field is independently auditable. -/
structure Construction where
  compiler : ∀ M : CanonicalFinalProof.PolyDTMCandidate,
    EffectiveDiagonalCompiler M
  tableau : P02BoundedComputationClose.TableauCompletenessCertificate
  sameInput :
    ∀ M : CanonicalFinalProof.PolyDTMCandidate,
      SameInputTransport M (compiler M)

/-- Bounded execution closes Cook-Levin correctness once tableau completeness is
provided. The only non-derived carrier field is same-input transport. -/
noncomputable def Construction.toProducer (C : Construction) :
    P02FinalProofProducer.Producer where
  compiler := C.compiler
  carrier := fun M =>
    { circuitOf := fun c =>
        rejectCircuit M ((C.sameInput M).selfInput c)
      selfInput := (C.sameInput M).selfInput }
  cook_levin_correct := by
    intro M c
    exact rejectCircuit_cook_levin_correct
      (boundedExec_of_tableauCompleteness C.tableau)
      M ((C.sameInput M).selfInput c)
  same_input_of_fixed := by
    intro M c hfixed
    exact (C.sameInput M).same_input_of_fixed c hfixed

/-- Once Construction is inhabited, the existing verified bridge yields the
terminal P02 target. -/
theorem construction_closes_p02 (C : Construction) :
    P02TerminalFrontier.P02Target :=
  C.toProducer.toP02Target

/-- The remaining live SSE mathematical obligation, with no literal BitString
fixed-point assumption. -/
def OpenMathObligation : Prop := Nonempty Construction

#print axioms MCore.Hardening.SSEWitnessConstruction.construction_closes_p02

end MCore.Hardening.SSEWitnessConstruction
