import MCore.Real.P01PhysicalDispatcherAudit
import MCore.Real.P01PhysicalRoutingAdapter
import MCore.Real.P01PhysicalEmbeddedRunMulti
import MCore.Real.P01FullVerifierPhysical

namespace MCore
namespace Real
namespace P01PhysicalGlobalRoutingFrontier

open P01PhysicalDispatcher
open P01PhysicalDispatcherAudit
open P01PhysicalRoutingAdapter
open P01PhysicalOperationControl
open P01FullVerifierPhysical

/-- Exact next implementation payload after the six local physical shards are
GREEN.  It requires a fixed finite-control machine that can actually enter the
local stack/witness/rewind bands and return to routing control.  No inhabitant
is asserted here. -/
structure GlobalRoutingCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  /-- The machine has one fixed initial state; no circuit/witness/index is
  encoded in finite control. -/
  fixed_initial : Fin (stateCount + 1)
  initial_eq : machine.initial = fixed_initial
  /-- Every abstract routing phase has a concrete entry state in the fixed
  finite state space. -/
  entry : RoutingControl -> Fin (stateCount + 1)
  /-- Entering readInput must be represented by an actual machine state. -/
  read_entry_exists :
    forall op : PhysicalOp,
      exists q, entry { op := op, phase := .readInput } = q
  /-- Entering a stack phase must be represented by an actual machine state. -/
  stack_entry_exists :
    forall op : PhysicalOp,
      exists q, entry { op := op, phase := .pop1 } = q
  /-- Rewind must be represented by an actual machine state. -/
  rewind_entry_exists :
    forall op : PhysicalOp,
      exists q, entry { op := op, phase := .rewind } = q
  /-- Global execution must not be trapped in the structural control band:
  at least one concrete transition from a routed entry crosses to a distinct
  state.  This is intentionally weak; semantic refinement is proved later. -/
  has_cross_phase_step :
    exists (ctrl : RoutingControl) (s : Option Bool),
      (machine.transition (entry ctrl) s).1 != entry ctrl

def GlobalRoutingGap : Prop := Nonempty GlobalRoutingCertificate

/-- The current structural dispatcher is not itself evidence that the global
routing gap is closed.  Its control transitions remain inside the control
band, exactly as certified by the existing audit. -/
theorem structural_dispatcher_requires_routing_payload :
    CrossPhaseRoutingPending :=
  crossPhaseRoutingPending

/-- Functional route targets are already total at the adapter level. -/
theorem route_target_total (ctrl : RoutingControl) :
    exists q : DispatcherState, routeEntryState ctrl = q := by
  exact ⟨routeEntryState ctrl, rfl⟩

#print axioms MCore.Real.P01PhysicalGlobalRoutingFrontier.structural_dispatcher_requires_routing_payload
#print axioms MCore.Real.P01PhysicalGlobalRoutingFrontier.route_target_total

end P01PhysicalGlobalRoutingFrontier
end Real
end MCore
