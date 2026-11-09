import MCore.Real.PNPHabitant
import MCore.Real.P01TerminalDelta

namespace MCore
namespace Real
namespace PNPCanonicalHabitantStatus

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open PNPHabitant
open P01TerminalDelta

abbrev CanonicalSATLanguage : BitLanguage :=
  SATBits circuitBitEncoding

/-- Exact current constructor: the local P01 terminal witness supplies mem_NP,
while the only mathematical separation payload is UniversalFailure on the same
canonical SAT language. -/
def canonicalHabitantOfP01AndLowerBound
    (p01 : IntegratedExecutionCertificate)
    (lb : UniversalFailure CanonicalSATLanguage) :
    CanonicalSATPNPHabitant where
  mem_NP := p01_terminal_gap_closes ⟨p01⟩
  lower_bound := lb

/-- Once both concrete fields exist, no further theorem-level gap remains. -/
theorem p01_and_lower_bound_close_pneqnp
    (p01 : IntegratedExecutionCertificate)
    (lb : UniversalFailure CanonicalSATLanguage) :
    PneqNP :=
  canonical_sat_habitant_closes
    (canonicalHabitantOfP01AndLowerBound p01 lb)

/-- Current exact fail-closed frontier.

The first conjunct is a formalization/engineering witness for SAT in NP in the
repository's hardened machine model.  The second conjunct is the mathematical
F2 separation payload. -/
def CanonicalSATCurrentFrontier : Prop :=
  P01TerminalGap ∧ UniversalFailure CanonicalSATLanguage

theorem current_frontier_closes
    (h : CanonicalSATCurrentFrontier) :
    PneqNP := by
  rcases h with ⟨⟨p01⟩, lb⟩
  exact p01_and_lower_bound_close_pneqnp p01 lb

/-- The mathematical OPEN_MATH_CORE remains exactly the universal deterministic
failure statement for canonical SAT. -/
def OpenMathCore : Prop :=
  UniversalFailure CanonicalSATLanguage

#print axioms MCore.Real.PNPCanonicalHabitantStatus.canonicalHabitantOfP01AndLowerBound
#print axioms MCore.Real.PNPCanonicalHabitantStatus.p01_and_lower_bound_close_pneqnp
#print axioms MCore.Real.PNPCanonicalHabitantStatus.current_frontier_closes

end PNPCanonicalHabitantStatus
end Real
end MCore
