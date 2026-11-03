import MCore.Real.P01WitnessPreservingPrep
import MCore.Real.P01VerifierGateMachine
import MCore.Real.P01FinalCertificate

namespace MCore
namespace Real
namespace P01IntegratedNTMFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P01WitnessPreservingPrep
open P01VerifierGateMachine
open P01FinalCertificate

/-!
Exact fail-closed decomposition of the remaining T1-D work.

The recovered witness-prep machine and gate evaluator are concrete components,
but neither file yet proves the operational theorems needed to instantiate
P01MachineConstruction.  This file names those missing proofs without
postulating or weakening the final endpoint.
-/

/-- Operational certificate still required for the recovered witness-prep NTM.
It must prove total polynomial halting from every canonical input. -/
structure WitnessPrepOperationalCertificate where
  halts :
    ∀ bits : BitString,
      witnessPreservingPrep.HaltsWithin
        (witnessPrepTimeBound bits.length)
        (initialNTMConfig witnessPreservingPrep bits)

/-- The recovered gate machine is only a one-gate evaluator.  A full verifier
must be a fixed finite-control TM/NTM over the canonical tape alphabet and
realize the full SAT witness relation, not merely one Boolean gate. -/
structure FullVerifierOperationalCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

/-- Exact terminal construction remains the existing hardened object. -/
abbrev IntegratedP01Construction := P01MachineConstruction

/-- No promotion occurs from component availability alone.  Only an actual
P01MachineConstruction closes T1-D. -/
theorem construction_only_closes
    (C : IntegratedP01Construction) :
    SATInNPGap circuitBitEncoding :=
  P01FinalCertificate.construction_closes_p01 ⟨C⟩

#print axioms MCore.Real.P01IntegratedNTMFrontier.construction_only_closes

end P01IntegratedNTMFrontier
end Real
end MCore
