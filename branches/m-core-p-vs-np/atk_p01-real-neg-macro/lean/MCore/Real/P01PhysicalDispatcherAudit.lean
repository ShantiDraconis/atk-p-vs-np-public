import MCore.Real.P01PhysicalDispatcher

namespace MCore
namespace Real
namespace P01PhysicalDispatcherAudit

open P01PhysicalDispatcher
open P01FullVerifierPhysicalControl

/-- The current union machine is intentionally only structural: a control
transition starting inside the verifier-control range remains in that same
range.  Therefore it does not yet dispatch into stack/read/rewind submachines. -/
theorem control_transition_stays_control
    (q : Fin 8) (s : Option Bool) :
    ∃ q' : Fin 8,
      (physicalDispatcherMachine.transition (controlState q) s).1 =
        controlState q' := by
  let t := decoderEvaluatorMachine.transition q s
  refine ⟨t.1, ?_⟩
  simp [physicalDispatcherMachine, controlState, asControl, liftControl, t]

/-- In particular, the structural union cannot by itself be the global
physical realization: cross-phase routing is a separate mandatory payload. -/
def CrossPhaseRoutingPending : Prop :=
  ∃ (q : Fin 8) (s : Option Bool),
    (physicalDispatcherMachine.transition (controlState q) s).1.val < 8

theorem crossPhaseRoutingPending :
    CrossPhaseRoutingPending := by
  refine ⟨decoderEvaluatorMachine.initial, none, ?_⟩
  rcases control_transition_stays_control decoderEvaluatorMachine.initial none with
    ⟨q', hq'⟩
  rw [hq']
  simp [controlState]

#print axioms MCore.Real.P01PhysicalDispatcherAudit.control_transition_stays_control
#print axioms MCore.Real.P01PhysicalDispatcherAudit.crossPhaseRoutingPending

end P01PhysicalDispatcherAudit
end Real
end MCore
