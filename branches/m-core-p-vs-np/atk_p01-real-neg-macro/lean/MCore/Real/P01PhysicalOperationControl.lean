import MCore.Real.P01PhysicalDispatcher
import MCore.Real.P01FullVerifierStackSemantics

namespace MCore
namespace Real
namespace P01PhysicalOperationControl

open P01PhysicalDispatcher
open P01FullVerifierStackSemantics

/-- Finite operation context. Arbitrary input indices remain encoded on tape. -/
inductive PhysicalOp where
  | input
  | constFalse
  | constTrue
  | neg
  | and
  | or
  deriving DecidableEq, Repr

/-- Small fixed routing phase; no Circuit, Nat index, witness or stack is stored
in finite control. -/
inductive RoutingPhase where
  | decode
  | readInput
  | pop1
  | pop2
  | push
  | rewind
  | done
  | reject
  deriving DecidableEq, Repr

/-- Context carried only by a finite opcode plus finite routing phase. -/
structure RoutingControl where
  op : PhysicalOp
  phase : RoutingPhase
  deriving DecidableEq, Repr

/-- The routing-control type is finite and independent of the input. -/
def routingStateCount : Nat := 6 * 8

/-- Semantic routing target for each logical instruction constructor. -/
def opOfInstr : EvalInstr → PhysicalOp
  | .input _ => .input
  | .const false => .constFalse
  | .const true => .constTrue
  | .neg => .neg
  | .and => .and
  | .or => .or

theorem opOfInstr_forgets_only_input_index
    (i j : Nat) :
    opOfInstr (.input i) = opOfInstr (.input j) := by
  rfl

theorem opOfInstr_const_false :
    opOfInstr (.const false) = .constFalse := rfl

theorem opOfInstr_const_true :
    opOfInstr (.const true) = .constTrue := rfl

theorem opOfInstr_neg :
    opOfInstr .neg = .neg := rfl

theorem opOfInstr_and :
    opOfInstr .and = .and := rfl

theorem opOfInstr_or :
    opOfInstr .or = .or := rfl

/-- Exact finite route skeleton. The next file connects these phases to the
already-certified submachines. -/
def initialRoutingPhase : PhysicalOp → RoutingPhase
  | .input => .readInput
  | .constFalse => .push
  | .constTrue => .push
  | .neg => .pop1
  | .and => .pop1
  | .or => .pop1

def afterFirstPop : PhysicalOp → RoutingPhase
  | .neg => .push
  | .and => .pop2
  | .or => .pop2
  | _ => .reject

def afterSecondPop : PhysicalOp → RoutingPhase
  | .and => .push
  | .or => .push
  | _ => .reject

#print axioms MCore.Real.P01PhysicalOperationControl.opOfInstr_forgets_only_input_index
#print axioms MCore.Real.P01PhysicalOperationControl.opOfInstr_const_false
#print axioms MCore.Real.P01PhysicalOperationControl.opOfInstr_const_true
#print axioms MCore.Real.P01PhysicalOperationControl.opOfInstr_neg
#print axioms MCore.Real.P01PhysicalOperationControl.opOfInstr_and
#print axioms MCore.Real.P01PhysicalOperationControl.opOfInstr_or

end P01PhysicalOperationControl
end Real
end MCore
