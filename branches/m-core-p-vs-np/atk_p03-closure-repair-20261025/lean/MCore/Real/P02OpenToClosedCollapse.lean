import MCore.Real.P02OpenClosedIrreflexiveCollapse

namespace MCore
namespace Real
namespace P02OpenToClosedCollapse

open CanonicalFinalProof
open P02DiagonalNoShortcut
open P02TerminalHabitantCycle
open P02OpenClosedDuality

/-- Final directed clause requested by the user. -/
def OpenTendsClosed : Prop := OpenMath → ClosedMath

/-- Because ClosedMath is defined as ¬OpenMath, the directed clause is exactly
a proof that OpenMath implies its own negation. -/
theorem open_tends_closed_iff_self_negating :
    OpenTendsClosed ↔ (OpenMath → ¬ OpenMath) := by
  rfl

/-- The directed clause alone entails ¬OpenMath. -/
theorem open_tends_closed_implies_not_open
    (h : OpenTendsClosed) :
    ¬ OpenMath := by
  intro ho
  exact h ho ho

/-- If OpenMath is also inhabited, the directed clause collapses to False. -/
theorem inhabited_open_plus_tends_closed_implies_false
    (ho : OpenMath)
    (h : OpenTendsClosed) :
    False := by
  exact h ho ho

/-- Therefore OpenMath -> ClosedMath cannot be used together with an inhabitant
of OpenMath to certify the endpoint; it destroys that inhabitant. -/
theorem open_tends_closed_excludes_endpoint_inhabitant
    (h : OpenTendsClosed) :
    ¬ Endpoint := by
  exact open_tends_closed_implies_not_open h

#print axioms MCore.Real.P02OpenToClosedCollapse.open_tends_closed_iff_self_negating
#print axioms MCore.Real.P02OpenToClosedCollapse.open_tends_closed_implies_not_open
#print axioms MCore.Real.P02OpenToClosedCollapse.inhabited_open_plus_tends_closed_implies_false
#print axioms MCore.Real.P02OpenToClosedCollapse.open_tends_closed_excludes_endpoint_inhabitant

end P02OpenToClosedCollapse
end Real
end MCore
