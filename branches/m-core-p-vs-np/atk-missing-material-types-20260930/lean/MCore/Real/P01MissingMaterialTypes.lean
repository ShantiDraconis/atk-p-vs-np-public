import MCore.Real.P01FinalCertificate
import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01EncodedStackEvaluator
import MCore.Real.P01EncodedFrameTape
import MCore.Real.CanonicalSATWitness
import MCore.Real.P01GapPreservingRead

namespace MCore
namespace Real
namespace P01MissingMaterialTypes

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01FinalCertificate
open P01EvalCursorMachine
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01GapPreservingRead
open P01WitnessIndexedReadPreserving

/-- Concrete witness assignment induced by the physical witness bitstring. -/
def witnessAssignment (witness : BitString) : Assignment :=
  fun i => witness.getD i false

/-- Exact remaining local P01 input-node producer.

The machine itself is the already-kernelized fixed-control `gapReadMachine`.
This certificate records only the substantive universal properties still needed
by the evaluator: exact indexed value, exact witness restoration, exact
tail/suffix preservation, and a uniform quadratic fuel bound. -/
structure PreservingUnaryWitnessReadCertificate : Prop where
  blank_none :
    gapReadMachine.blank = none

  exact_run :
    ∀ (witness tail : BitString) (k i : Nat)
      (suffix : List (Option Bool)),
      i < witness.length →
      gapReadMachine.run (gapReadFuel k i)
          (gapReadConfig witness k i tail suffix) =
        { state := .halt (witness.getD i false),
          tape :=
            { left := witness.map some,
              head := none,
              right :=
                List.replicate (k + i + 1) none ++
                  (tail.map some ++ suffix) } }

  fuel_quadratic :
    ∀ k i : Nat,
      gapReadFuel k i ≤
        6 * ((k + i + 2) * (k + i + 2))

/-- Material inhabitant of the sole remaining local input-read obligation.
No endpoint assumption is consumed: both fields are discharged by the
kernelized gap-preserving reader theorems. -/
def preservingUnaryWitnessReadCertificate :
    PreservingUnaryWitnessReadCertificate where
  blank_none := rfl
  exact_run := by
    intro witness tail k i suffix hi
    exact gapRead_forall witness tail k i suffix hi
  fuel_quadratic := gapReadFuel_le

def PreservingUnaryWitnessReadGap : Prop :=
  Nonempty PreservingUnaryWitnessReadCertificate

theorem preservingUnaryWitnessReadGap_closed :
    PreservingUnaryWitnessReadGap :=
  ⟨preservingUnaryWitnessReadCertificate⟩

#print axioms MCore.Real.P01MissingMaterialTypes.preservingUnaryWitnessReadCertificate
#print axioms MCore.Real.P01MissingMaterialTypes.preservingUnaryWitnessReadGap_closed

/-- Exact global physical-verifier producer after all local evalStep cases are
refined.  A valid inhabitant must execute the frozen evaluator semantics with
one fixed TM, preserve the witness, consume exactly the encoded circuit, empty
the continuation stack, and return the exact Boolean circuit value. -/
structure PhysicalEvalRunCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none

  result : Fin (stateCount + 1) → Option Bool

  padding : BitString → CircuitK1.Circuit → Nat

  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  halts :
    ∀ (witness : BitString) (c : CircuitK1.Circuit),
      let source := encodeCircuit c
      let pad := padding witness c
      let inputSize := witness.length + source.length + pad
      machine.HaltsWithin (timeBound inputSize)
        { state := machine.initial,
          tape :=
            evalCursorStackEndTape witness 0 source [] pad }

  refines_evalRun :
    ∀ (witness : BitString) (c : CircuitK1.Circuit),
      let source := encodeCircuit c
      let pad := padding witness c
      let inputSize := witness.length + source.length + pad
      let final :=
        machine.run (timeBound inputSize)
          { state := machine.initial,
            tape :=
              evalCursorStackEndTape witness 0 source [] pad }
      result final.state =
          some (evalCircuit (witnessAssignment witness) c) ∧
        final.tape =
          evalCursorStackEndTape
            witness source.length [] [] pad

/-- OPEN implementation target for the one-machine global verifier simulation. -/
def PhysicalEvalRunGap : Prop :=
  Nonempty PhysicalEvalRunCertificate

end P01MissingMaterialTypes
end Real
end MCore
