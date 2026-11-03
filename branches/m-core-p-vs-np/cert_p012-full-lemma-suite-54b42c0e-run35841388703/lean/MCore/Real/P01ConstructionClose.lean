import MCore.Real.P01VerifierComposition
import MCore.Real.P01FinalCertificate

namespace MCore
namespace Real
namespace P01ConstructionClose

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P01FinalCertificate

/-!
T1.4 fail-closed terminal boundary.

T1.1, T1.2 and T1.3 now provide:
* a no-hypothesis canonical parser simulation;
* a finite-control nondeterministic witness generator with polynomial bound;
* exact verifier semantics and the SATBits witness relation.

The remaining theorem is intentionally not manufactured here. To close T1,
the repository must define a concrete P01MachineConstruction whose single
canonical NTM implements the full parser -> witness -> verifier execution and
proves total polynomial halting plus exact SATBits acceptance.

This file keeps that delta explicit and provides only the sound promotion map.
-/

/-- Exact remaining T1 terminal obligation. -/
abbrev IntegratedSATNTMConstruction :=
  P01MachineConstruction

/-- A genuine integrated construction closes the canonical SAT-in-NP gate. -/
theorem integrated_construction_closes_T1
    (C : IntegratedSATNTMConstruction) :
    CanonicalSATNTMAttack.CanonicalSATMachineClosure :=
  construction_closes_p01 ⟨C⟩

/-- The final endpoint after T1 is exactly SATInNPGap for the canonical encoding. -/
theorem integrated_construction_gives_sat_in_np
    (C : IntegratedSATNTMConstruction) :
    SATInNPGap circuitBitEncoding :=
  integrated_construction_closes_T1 C

#print axioms MCore.Real.P01ConstructionClose.integrated_construction_closes_T1
#print axioms MCore.Real.P01ConstructionClose.integrated_construction_gives_sat_in_np

end P01ConstructionClose
end Real
end MCore
