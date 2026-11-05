import MCore.Real.P01PhysicalVerifierUniformCosts
import MCore.Real.P01WitnessGuessExecution
import MCore.Real.P01WitnessBoundNormalization
import MCore.Real.P01T1DPhysicalAssembly
import MCore.Real.P01T1DGlobalPhysical
import MCore.Real.P01FullVerifierReverseDecoderGap
import MCore.Real.P01FullVerifierPhysicalOps
import MCore.Real.P01FullVerifierShuttleReturn
import MCore.Real.P01FullVerifierInputShuttleV2
import MCore.Real.P01FullVerifierStackPrimitiveMachine
import MCore.Real.P01FullVerifierPhysical
import MCore.Real.P01FullVerifierPhysicalRefinement
import MCore.Real.P01FullVerifierPhysicalRefinementV2
import MCore.Real.P01FullVerifierPhysicalStackV2
import MCore.Real.P01PhysicalVerifierBudget
import MCore.Real.P01PhysicalVerifierFoundations

namespace MCore
namespace Real
namespace P01PhysicalRealizationAssembly

open CanonicalFinalProof
open P01FullVerifierPhysical
open P01FullVerifierPhysicalRefinement
open P01FullVerifierPhysicalStackV2

/-- Exact machine-level fields still needed after the tape/refinement algebra
has been closed. This separates implementation from the already-proved stack
representation lemmas. -/
structure PhysicalMachineCore where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts :
    ∀ (phi : CircuitK1.Circuit) (w : CanonicalSATWitness.SATWitness phi),
      machine.HaltsWithin
        (timeBound (CanonicalCircuitBits.encodeCircuit phi).length)
        { state := machine.initial,
          tape := P01FullVerifierMachine.verifierInputTape
            (CanonicalSATWitness.witnessBits w)
            (CanonicalCircuitBits.encodeCircuit phi) }
  correct :
    ∀ (phi : CircuitK1.Circuit) (w : CanonicalSATWitness.SATWitness phi),
      accepting
        (machine.run
          (timeBound (CanonicalCircuitBits.encodeCircuit phi).length)
          { state := machine.initial,
            tape := P01FullVerifierMachine.verifierInputTape
              (CanonicalSATWitness.witnessBits w)
              (CanonicalCircuitBits.encodeCircuit phi) }).state = true ↔
        CanonicalSATVerifier.verifyWitness phi w = true

def PhysicalMachineCore.toRealization
    (C : PhysicalMachineCore) : PhysicalVerifierRealization where
  stateCount := C.stateCount
  machine := C.machine
  blank_none := C.blank_none
  accepting := C.accepting
  timeBound := C.timeBound
  time_poly := C.time_poly
  halts := C.halts
  physical_eq_logical := C.correct

theorem physicalMachineCore_closes_full_verifier
    (C : PhysicalMachineCore) :
    P01FullVerifierMachine.FullVerifierGap := by
  exact physical_realization_closes_full_verifier C.toRealization

#print axioms MCore.Real.P01PhysicalRealizationAssembly.physicalMachineCore_closes_full_verifier

end P01PhysicalRealizationAssembly
end Real
end MCore
