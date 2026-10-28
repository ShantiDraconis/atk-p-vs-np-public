import MCore.Real.P01WitnessPreservingPrep
import MCore.Real.P01VerifierGateMachine
import MCore.Real.P01VerifierComposition
import MCore.Real.P01FinalCertificate

namespace MCore
namespace Real
namespace P01IntegratedNTMRequirements

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open CanonicalSATVerifier
open P01FinalCertificate

/-!
Terminal T1-D requirements extracted from the concrete recovered components.

This file does not weaken P01MachineConstruction and does not promote T1.
It records the exact machine-level facts still required before the single
integrated NTM can be constructed without assumptions.
-/

/-- The witness-preparation machine needs a global execution theorem, not only
local transition lemmas: every branch must halt within its cubic budget and
the reached tapes must have the documented prepared layout for some witness. -/
structure WitnessPrepExecutionCertificate where
  halts : ∀ source : BitString,
    P01WitnessPreservingPrep.witnessPreservingPrep.HaltsWithin
      (P01WitnessPreservingPrep.witnessPrepTimeBound source.length)
      (initialNTMConfig P01WitnessPreservingPrep.witnessPreservingPrep source)
  reached_layout : ∀ source : BitString,
    ∀ reached ∈
      P01WitnessPreservingPrep.witnessPreservingPrep.runBranches
        (P01WitnessPreservingPrep.witnessPrepTimeBound source.length)
        [initialNTMConfig P01WitnessPreservingPrep.witnessPreservingPrep source],
      ∃ witness : BitString,
        reached.tape = P01WitnessPreservingPrep.preparedTape witness source

/-- A terminal verifier component must evaluate the whole decoded circuit
against the guessed witness on the canonical tape. The current gate machine
only proves one AND/OR gate evaluation, so this is deliberately stronger. -/
structure FullVerifierMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts : ∀ (phi : CircuitK1.Circuit) (w : SATWitness phi), True
  correct : ∀ (phi : CircuitK1.Circuit) (w : SATWitness phi),
    verifyWitness phi w = true ↔ SATWitnessAccepts phi w

/-- T1-D remains the original hardened endpoint. These requirements are
diagnostic only and are not accepted as substitutes for the integrated NTM. -/
abbrev T1DTarget := P01MachineConstruction

#print axioms MCore.Real.P01IntegratedNTMRequirements.T1DTarget

end P01IntegratedNTMRequirements
end Real
end MCore
