import MCore.Real.P02TableauSourceRecovery
import MCore.Real.PNPNTMTableauEncoding

namespace P02
namespace LANE4
namespace AUX
namespace Recoverability

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding
open MCore.Real.P02TableauSourceRecovery

/-- R1, reused from the audited MCore module. -/
theorem inputTape_injective :
    Function.Injective inputTape :=
  MCore.Real.P02TableauSourceRecovery.inputTape_injective

/-- Literal encoding injectivity, reused. -/
theorem ntmLiteralCircuit_injective :
    Function.Injective ntmLiteralCircuit :=
  MCore.Real.P02TableauSourceRecovery.ntmLiteralCircuit_injective

/-- Clause encoding injectivity, reused. -/
theorem ntmClauseCircuit_injective :
    Function.Injective ntmClauseCircuit :=
  MCore.Real.P02TableauSourceRecovery.ntmClauseCircuit_injective

/-- R3, reused from the audited MCore module. -/
theorem ntmCNFCircuit_injective :
    Function.Injective ntmCNFCircuit :=
  MCore.Real.P02TableauSourceRecovery.ntmCNFCircuit_injective

/-
R2/R4/R5 are intentionally not postulated here.

The current Circuit datatype has no `Circuit.inputLen` field and no
`Circuit.extractInput` operation.  Therefore dimension/source recovery must
be derived from the concrete tableau syntax before those theorems can be
inhabited without axioms.
-/

#print axioms P02.LANE4.AUX.Recoverability.inputTape_injective
#print axioms P02.LANE4.AUX.Recoverability.ntmLiteralCircuit_injective
#print axioms P02.LANE4.AUX.Recoverability.ntmClauseCircuit_injective
#print axioms P02.LANE4.AUX.Recoverability.ntmCNFCircuit_injective

end Recoverability
end AUX
end LANE4
end P02
