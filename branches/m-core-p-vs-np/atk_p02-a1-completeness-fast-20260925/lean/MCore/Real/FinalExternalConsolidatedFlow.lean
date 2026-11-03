import MCore.Real.P01FinalCertificate
import MCore.Real.P02G21G22Attack
import MCore.Real.P02KleeneBridge
import MCore.Real.P02KleeneCookLevinBridge
import MCore.Real.P02ResidualSameInputBridge
import MCore.Real.P02BoundedComputationClose
import MCore.Real.P02SemanticMismatchAlgebra
import MCore.Real.FinalExternalLiveTwoProducer
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace FinalExternalConsolidatedFlow

open CanonicalFinalProof
open P01FinalCertificate
open P02G21G22Attack
open P02KleeneBridge
open P02KleeneCookLevinBridge

/--
Exact producer package required by the consolidated route.
This structure is fail-closed: it contains only already-existing terminal
propositions and does not create replacement notions of P01/P02/G3.
-/
structure ConsolidatedExternalInputs where
  p01 : P01ConstructionGap
  p02 : P02TerminalFrontier.P02Target
  g3 : G3ExternalContract

/-- The P01 producer is promoted only through the repository's existing
construction theorem. -/
theorem p01_from_consolidated
    (I : ConsolidatedExternalInputs) :
    SATInNPGap circuitBitEncoding := by
  exact construction_closes_p01 I.p01

/-- The P02 producer is already the exact pinned terminal proposition. -/
theorem p02_from_consolidated
    (I : ConsolidatedExternalInputs) :
    P02TerminalFrontier.P02Target :=
  I.p02

/--
The consolidated route is intentionally only a wiring layer.
Actual FinalExternalCertificate construction remains delegated to the
repository's existing certificate/producer modules.
-/
def ConsolidatedExternalGap : Prop :=
  Nonempty ConsolidatedExternalInputs

/-
Current required producers:
1. P01ConstructionGap
2. P02Target
3. G3ExternalContract

Known reusable infrastructure now included in the active lane:
- P01WitnessIndexedRead*
- P02BoundedComputation*
- P02KleeneE1 / P02KleeneBridgeAudit
- P02SemanticMismatchAlgebra
- FinalExternalLiveTwoProducer
- ResidualRotationAlgebra -> ResidualSameInputInvariant bridge

OPEN terminal obligations remain outside this wiring layer.
-/

#print axioms MCore.Real.FinalExternalConsolidatedFlow.p01_from_consolidated
#print axioms MCore.Real.FinalExternalConsolidatedFlow.p02_from_consolidated

end FinalExternalConsolidatedFlow
end Real
end MCore
