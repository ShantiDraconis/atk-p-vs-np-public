import MCore.Real.P02TerminalThreeWayCenter

namespace MCore
namespace Real
namespace P02TerminalFractionConvergence

open CanonicalFinalProof
open P02DiagonalNoShortcut
open P02TerminalHabitantCycle
open P02TerminalConjunctureNucleus
open P02TerminalThreeWayCenter

/-- Two explicit terminal convergence codes requested for the final nucleus. -/
inductive FractionRoute
  | zeroOverOne
  | oneOverOne
  | zeroOverTwo
  | twoOverTwo
  deriving DecidableEq, Repr

def converge : FractionRoute → FractionRoute
  | .zeroOverOne => .oneOverOne
  | .oneOverOne  => .oneOverOne
  | .zeroOverTwo => .twoOverTwo
  | .twoOverTwo  => .twoOverTwo

theorem zero_one_converges :
    converge .zeroOverOne = .oneOverOne := rfl

theorem zero_two_converges :
    converge .zeroOverTwo = .twoOverTwo := rfl

theorem one_one_fixed :
    converge .oneOverOne = .oneOverOne := rfl

theorem two_two_fixed :
    converge .twoOverTwo = .twoOverTwo := rfl

/-- Every route carries the same terminal mathematical payload. -/
def routePayload : FractionRoute → Prop
  | .zeroOverOne => Endpoint
  | .oneOverOne  => Endpoint
  | .zeroOverTwo => Endpoint
  | .twoOverTwo  => Endpoint

theorem route_payload_is_endpoint
    (r : FractionRoute) :
    routePayload r ↔ Endpoint := by
  cases r <;> rfl

/-- Convergence changes only the label, never the terminal proposition. -/
theorem convergence_preserves_endpoint
    (r : FractionRoute) :
    routePayload (converge r) ↔ routePayload r := by
  cases r <;> rfl

/-- Both requested convergence paths hit fixed representatives of the same
terminal signature. -/
theorem two_fraction_paths_same_terminal :
    routePayload (converge .zeroOverOne) ↔
      routePayload (converge .zeroOverTwo) := by
  rfl

/-- Negative control: convergence of labels to fixed representatives does not
create a proof object for an arbitrary proposition. -/
def FractionConvergenceCreatesInhabitant : Prop :=
  ∀ P : Prop,
    (FractionRoute → Prop) →
    P

theorem fraction_convergence_does_not_create_inhabitant :
    ¬ FractionConvergenceCreatesInhabitant := by
  intro H
  exact H False (fun _ => False)

/-- If the endpoint is inhabited, all four route labels are inhabited. -/
theorem endpoint_inhabits_fraction_routes
    (h : Endpoint) :
    ∀ r : FractionRoute, routePayload r := by
  intro r
  exact (route_payload_is_endpoint r).2 h

#print axioms MCore.Real.P02TerminalFractionConvergence.zero_one_converges
#print axioms MCore.Real.P02TerminalFractionConvergence.zero_two_converges
#print axioms MCore.Real.P02TerminalFractionConvergence.convergence_preserves_endpoint
#print axioms MCore.Real.P02TerminalFractionConvergence.two_fraction_paths_same_terminal
#print axioms MCore.Real.P02TerminalFractionConvergence.fraction_convergence_does_not_create_inhabitant
#print axioms MCore.Real.P02TerminalFractionConvergence.endpoint_inhabits_fraction_routes

end P02TerminalFractionConvergence
end Real
end MCore
