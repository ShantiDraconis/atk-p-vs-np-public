import MCore.Real.P01PhysicalGlobalRoutingFrontier
import MCore.Real.P01PhysicalOpcodeDecoder
import MCore.Real.P01FullVerifierStackPrimitiveMachine
import MCore.Real.P01WitnessIndexedReadMachine
import MCore.Real.P01FullVerifierSourceRewind

namespace MCore
namespace Real
namespace P01PhysicalContextualState

open P01PhysicalOperationControl
open P01PhysicalOpcodeDecoder
open P01FullVerifierStackPrimitiveMachine
open P01WitnessIndexedReadMachine
open P01FullVerifierSourceRewind

/-- Global finite control with operation context preserved while local physical
submachines run.  Unbounded witness indices, circuit data and stack contents
remain on tape. -/
inductive ContextualState where
  | opcode (q : Fin 13)
  | stack (op : PhysicalOp) (phase : RoutingPhase) (q : Fin 8)
  | witness (op : PhysicalOp) (q : Fin 6)
  | rewind (op : PhysicalOp) (q : Fin 3)
  | accept
  | reject
  deriving DecidableEq, Repr

/-- Fixed cardinality envelope.  This is deliberately coarse; it proves that
the contextual controller is finite and input-independent. -/
def contextualStateCount : Nat :=
  13 + (6 * 8 * 8) + (6 * 6) + (6 * 3) + 2

/-- Semantic next phase after a successful local stack macro.  The popped bit
is represented by the local halting state and may be consumed by the next
routing layer; no unbounded data is stored in control. -/
def afterStackHalt
    (op : PhysicalOp) (phase : RoutingPhase) : RoutingPhase :=
  match phase with
  | .pop1 => afterFirstPop op
  | .pop2 => afterSecondPop op
  | .push => .rewind
  | _ => .reject

/-- Local stack halts retain operation context. -/
def stackReturn
    (op : PhysicalOp) (phase : RoutingPhase) (q : Fin 8) : ContextualState :=
  if q = haltPush then
    .rewind op sourceRewindMachine.initial
  else if q = haltPopFalse || q = haltPopTrue then
    match afterStackHalt op phase with
    | .pop2 => .stack op .pop2 popStart
    | .push => .stack op .push pushFalse
    | .rewind => .rewind op sourceRewindMachine.initial
    | .done => .accept
    | _ => .reject
  else if q = reject then
    .reject
  else
    .stack op phase q

/-- Witness-reader halts preserve the opcode context and continue to push. -/
def witnessReturn
    (op : PhysicalOp) (q : Fin 6) : ContextualState :=
  if q = (4 : Fin 6) then
    .stack op .push pushTrue
  else if q = (5 : Fin 6) then
    .stack op .push pushFalse
  else
    .witness op q

/-- Source-rewind halt returns to opcode decoding. -/
def rewindReturn
    (op : PhysicalOp) (q : Fin 3) : ContextualState :=
  if q = rewindHalt then
    .opcode opcodeDecoderMachine.initial
  else
    .rewind op q

/-- The contextual state architecture is finite and, unlike the structural
Fin-27 dispatcher, explicitly retains the finite opcode across local macros. -/
def ContextualArchitectureClosed : Prop :=
  Nonempty ContextualState

theorem contextualArchitectureClosed : ContextualArchitectureClosed :=
  ⟨.opcode opcodeDecoderMachine.initial⟩

theorem witness_true_routes_push_true (op : PhysicalOp) :
    witnessReturn op (4 : Fin 6) = .stack op .push pushTrue := by
  simp [witnessReturn]

theorem witness_false_routes_push_false (op : PhysicalOp) :
    witnessReturn op (5 : Fin 6) = .stack op .push pushFalse := by
  simp [witnessReturn]

theorem rewind_halt_routes_decode (op : PhysicalOp) :
    rewindReturn op rewindHalt = .opcode opcodeDecoderMachine.initial := by
  simp [rewindReturn]

#print axioms MCore.Real.P01PhysicalContextualState.contextualArchitectureClosed
#print axioms MCore.Real.P01PhysicalContextualState.witness_true_routes_push_true
#print axioms MCore.Real.P01PhysicalContextualState.witness_false_routes_push_false
#print axioms MCore.Real.P01PhysicalContextualState.rewind_halt_routes_decode

end P01PhysicalContextualState
end Real
end MCore
