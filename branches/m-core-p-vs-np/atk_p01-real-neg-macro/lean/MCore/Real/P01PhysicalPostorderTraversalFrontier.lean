import MCore.Real.CanonicalCircuitBits
import MCore.Real.CanonicalSATFrameAttack
import MCore.Real.P01FullVerifierStackSemantics

namespace MCore
namespace Real
namespace P01PhysicalPostorderTraversalFrontier

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATFrameAttack
open P01FullVerifierStackSemantics

/-- Canonical physical encoding of evaluator instructions.  It reuses the
three-bit opcode tags; arbitrary input indices remain unary data on tape. -/
def encodeEvalInstr : EvalInstr -> BitString
  | .input i     => [false, false, false] ++ encodeNat i
  | .const false => [false, false, true]
  | .const true  => [false, true, false]
  | .neg         => [false, true, true]
  | .and         => [true, false, false]
  | .or          => [true, false, true]

def encodeEvalProgram (program : List EvalInstr) : BitString :=
  program.flatMap encodeEvalInstr

/-- The source encoding is prefix-order, while the evaluator program is
postorder.  This concrete regression prevents the direct opcode-scan route
from being promoted as a verifier implementation. -/
theorem direct_prefix_execution_falsified :
    encodeCircuit (.not (.const false)) !=
      encodeEvalProgram (evalProgram (.not (.const false))) := by
  decide

/-- Exact machine-level payload required before global halting can be proved.
The machine must transform canonical prefix circuit input into the postorder
instruction stream consumed by the already-certified evaluator semantics. -/
structure PhysicalPostorderTraversalCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts :
    forall phi : Circuit,
      machine.HaltsWithin
        (timeBound (encodeCircuit phi).length)
        (initialTMConfig machine (encodeCircuit phi))
  correct :
    forall phi : Circuit,
      TapeRepresents
        (encodeEvalProgram (evalProgram phi))
        (machine.run
          (timeBound (encodeCircuit phi).length)
          (initialTMConfig machine (encodeCircuit phi))).tape

def PhysicalPostorderTraversalGap : Prop :=
  Nonempty PhysicalPostorderTraversalCertificate

/-- Functional target is completely fixed already; only its physical
finite-control realization remains open. -/
def functionalPostorderTarget (phi : Circuit) : BitString :=
  encodeEvalProgram (evalProgram phi)

theorem functionalPostorderTarget_spec (phi : Circuit) :
    functionalPostorderTarget phi =
      encodeEvalProgram (evalProgram phi) := by
  rfl

#print axioms MCore.Real.P01PhysicalPostorderTraversalFrontier.direct_prefix_execution_falsified
#print axioms MCore.Real.P01PhysicalPostorderTraversalFrontier.functionalPostorderTarget_spec

end P01PhysicalPostorderTraversalFrontier
end Real
end MCore
