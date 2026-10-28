import MCore.Real.P01PhysicalOperationControl
import MCore.Real.P01PhysicalDispatcher

namespace MCore
namespace Real
namespace P01PhysicalRoutingAdapter

open P01PhysicalOperationControl
open P01PhysicalDispatcher
open P01FullVerifierStackPrimitiveMachine
open P01WitnessIndexedReadMachine
open P01FullVerifierSourceRewind

/-- Entry state selected for a finite routing phase. -/
def routeEntryState
    (ctrl : RoutingControl) : DispatcherState :=
  match ctrl.phase with
  | .decode    => controlState P01FullVerifierPhysicalControl.decodeInstr
  | .readInput => witnessReadState witnessIndexedReadMachine.initial
  | .pop1      => stackState popStart
  | .pop2      => stackState popStart
  | .push      =>
      match ctrl.op with
      | .constTrue => stackState pushTrue
      | _          => stackState pushFalse
  | .rewind    => rewindState sourceRewindMachine.initial
  | .done      => acceptState
  | .reject    => rejectState

theorem input_routes_to_reader :
    routeEntryState
      { op := .input, phase := initialRoutingPhase .input } =
      witnessReadState witnessIndexedReadMachine.initial := by
  rfl

theorem const_false_routes_to_push_false :
    routeEntryState
      { op := .constFalse, phase := initialRoutingPhase .constFalse } =
      stackState pushFalse := by
  rfl

theorem const_true_routes_to_push_true :
    routeEntryState
      { op := .constTrue, phase := initialRoutingPhase .constTrue } =
      stackState pushTrue := by
  rfl

theorem neg_routes_to_first_pop :
    routeEntryState
      { op := .neg, phase := initialRoutingPhase .neg } =
      stackState popStart := by
  rfl

theorem and_routes_to_first_pop :
    routeEntryState
      { op := .and, phase := initialRoutingPhase .and } =
      stackState popStart := by
  rfl

theorem or_routes_to_first_pop :
    routeEntryState
      { op := .or, phase := initialRoutingPhase .or } =
      stackState popStart := by
  rfl

theorem neg_after_first_pop_routes_push :
    routeEntryState
      { op := .neg, phase := afterFirstPop .neg } =
      stackState pushFalse := by
  rfl

theorem and_after_first_pop_routes_second_pop :
    routeEntryState
      { op := .and, phase := afterFirstPop .and } =
      stackState popStart := by
  rfl

theorem or_after_first_pop_routes_second_pop :
    routeEntryState
      { op := .or, phase := afterFirstPop .or } =
      stackState popStart := by
  rfl

theorem and_after_second_pop_routes_push :
    routeEntryState
      { op := .and, phase := afterSecondPop .and } =
      stackState pushFalse := by
  rfl

theorem or_after_second_pop_routes_push :
    routeEntryState
      { op := .or, phase := afterSecondPop .or } =
      stackState pushFalse := by
  rfl

/-- Routing state is always one of the fixed finite dispatcher states. -/
theorem routeEntryState_bounded
    (ctrl : RoutingControl) :
    (routeEntryState ctrl).val < 27 := by
  exact (routeEntryState ctrl).isLt

#print axioms MCore.Real.P01PhysicalRoutingAdapter.input_routes_to_reader
#print axioms MCore.Real.P01PhysicalRoutingAdapter.const_false_routes_to_push_false
#print axioms MCore.Real.P01PhysicalRoutingAdapter.const_true_routes_to_push_true
#print axioms MCore.Real.P01PhysicalRoutingAdapter.neg_routes_to_first_pop
#print axioms MCore.Real.P01PhysicalRoutingAdapter.and_routes_to_first_pop
#print axioms MCore.Real.P01PhysicalRoutingAdapter.or_routes_to_first_pop
#print axioms MCore.Real.P01PhysicalRoutingAdapter.routeEntryState_bounded

end P01PhysicalRoutingAdapter
end Real
end MCore
