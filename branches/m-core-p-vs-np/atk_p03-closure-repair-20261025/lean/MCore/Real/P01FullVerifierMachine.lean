import MCore.Real.P01VerifierGateMachine
import MCore.Real.P01FullVerifierTraversal
import MCore.Real.P01WitnessPreservingPrep
import MCore.Real.P01VerifierComposition
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P01FullVerifierMachine

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open CanonicalSATVerifier

/-!
T1-D full-verifier target.

The final verifier must be one fixed finite-control machine.  It therefore
cannot store an arbitrary Circuit or witness in its control state and cannot
be defined as `fullVerifierMachine (phi : Circuit) (w : Witness)`.

It must instead read the canonical encoded source and guessed witness from the
single tape, traverse the prefix encoding, evaluate all input/const/not/and/or
nodes, and halt with acceptance exactly when `verifyWitness` is true.
-/

/-- Canonical verifier input layout inherited from witness preparation. -/
def verifierInputTape (witness source : BitString) : Tape (Option Bool) :=
  P01WitnessPreservingPrep.preparedTape witness source

/-- Exact fixed-machine payload required from the full verifier. -/
structure FullVerifierCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  halts : ∀ (phi : CircuitK1.Circuit) (w : SATWitness phi),
    machine.HaltsWithin
      (timeBound (encodeCircuit phi).length)
      { state := machine.initial, tape := verifierInputTape (witnessBits w) (encodeCircuit phi) }

  correct : ∀ (phi : CircuitK1.Circuit) (w : SATWitness phi),
    accepting
      (machine.run
        (timeBound (encodeCircuit phi).length)
        { state := machine.initial, tape := verifierInputTape (witnessBits w) (encodeCircuit phi) }).state = true ↔
      verifyWitness phi w = true

/-- The recovered three-step gate machine is a certified local primitive.
It is intentionally not promoted to FullVerifierCertificate. -/
theorem gate_primitive_exact
    (isOr a b : Bool) :
    let final :=
      P01VerifierGateMachine.gateEvalMachine.run 3
        (initialTMConfig P01VerifierGateMachine.gateEvalMachine
          (P01VerifierGateMachine.gateCommand isOr a b))
    final.state = (7 : Fin 9) ∧
      final.tape.head = some (P01VerifierGateMachine.gateResult isOr a b) :=
  P01VerifierGateMachine.gateEval_run isOr a b

/-- A completed fixed verifier immediately recovers the already-certified
high-level verifier semantics on canonical encodings. -/
theorem full_verifier_semantics
    (V : FullVerifierCertificate)
    (phi : CircuitK1.Circuit)
    (w : SATWitness phi) :
    V.accepting
      (V.machine.run
        (V.timeBound (encodeCircuit phi).length)
        { state := V.machine.initial,
          tape := verifierInputTape (witnessBits w) (encodeCircuit phi) }).state = true ↔
      SATWitnessAccepts phi w :=
  (V.correct phi w).trans (P01VerifierComposition.verifier_correct phi w)

/-- This remains the exact open construction object for the verifier phase. -/
def FullVerifierGap : Prop :=
  Nonempty FullVerifierCertificate

#print axioms MCore.Real.P01FullVerifierMachine.gate_primitive_exact
#print axioms MCore.Real.P01FullVerifierMachine.full_verifier_semantics

end P01FullVerifierMachine
end Real
end MCore
