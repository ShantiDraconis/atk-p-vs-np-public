import MCore.Real.CanonicalSATFrameAttack
import MCore.Real.PNPNTMTableauEncoding
import MCore.Real.P02TableauSourceRecovery

namespace P02
namespace LANE4
namespace AUX
namespace R1_R3_REAL

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.CanonicalSATFrameAttack
open MCore.Real.PNPNTMTableauEncoding

/-- R1: canonical input-tape encoding is injective. -/
theorem inputTape_injective :
    Function.Injective inputTape := by
  intro x y hxy
  have h := congrArg tapeWord hxy
  simpa using h

/-- R3a: literal-to-circuit encoding is injective. -/
theorem ntmLiteralCircuit_injective :
    Function.Injective ntmLiteralCircuit := by
  exact MCore.Real.P02TableauSourceRecovery.ntmLiteralCircuit_injective

/-- R3b: clause-to-circuit encoding is injective. -/
theorem ntmClauseCircuit_injective :
    Function.Injective ntmClauseCircuit := by
  exact MCore.Real.P02TableauSourceRecovery.ntmClauseCircuit_injective

/-- R3c: CNF-to-circuit encoding is injective. -/
theorem ntmCNFCircuit_injective :
    Function.Injective ntmCNFCircuit := by
  exact MCore.Real.P02TableauSourceRecovery.ntmCNFCircuit_injective

#print axioms P02.LANE4.AUX.R1_R3_REAL.inputTape_injective
#print axioms P02.LANE4.AUX.R1_R3_REAL.ntmLiteralCircuit_injective
#print axioms P02.LANE4.AUX.R1_R3_REAL.ntmClauseCircuit_injective
#print axioms P02.LANE4.AUX.R1_R3_REAL.ntmCNFCircuit_injective

end R1_R3_REAL
end AUX
end LANE4
end P02
