import MCore.Real.P02DiagonalNoShortcut
import MCore.Real.P02FinalRootConditional

namespace MCore
namespace Real
namespace P02TerminalRecurrenceTheorem

open CanonicalFinalProof
open P02DiagonalNoShortcut
open P02FinalRootConditional

/-- The active mathematical endpoint and the active gap have the same
terminal signature. This is a classification theorem, not an inhabitant. -/
abbrev TerminalEndpoint : Prop := CandidateCodeSemanticFixedPoint
abbrev TerminalGap : Prop := CandidateCodeSemanticFixedPoint

theorem terminal_endpoint_iff_gap :
    TerminalEndpoint ↔ TerminalGap := by
  rfl

/-- Re-expanding a proposition only through an identity return carries no
new mathematical content. -/
def IdentityExpansion (P : Prop) : Prop := P

theorem identity_expansion_fixed
    (P : Prop) :
    IdentityExpansion P ↔ P := by
  rfl

/-- At the active frontier, another identity-style expansion returns exactly
to the same terminal statement. -/
theorem terminal_recurrence_signature :
    IdentityExpansion TerminalEndpoint ↔ TerminalEndpoint := by
  rfl

/-- The final root consumes precisely the terminal endpoint; there is no
additional active bridge after this point. -/
theorem terminal_endpoint_closes_final_root
    (h : TerminalEndpoint) :
    PneqNP := by
  exact FINAL_ROOT h

/-- Any proof object for the terminal gap is exactly a proof object for the
terminal endpoint, because they are definitionally the same proposition. -/
theorem terminal_gap_to_endpoint
    (h : TerminalGap) :
    TerminalEndpoint := h

theorem terminal_endpoint_to_gap
    (h : TerminalEndpoint) :
    TerminalGap := h

#print axioms MCore.Real.P02TerminalRecurrenceTheorem.terminal_endpoint_iff_gap
#print axioms MCore.Real.P02TerminalRecurrenceTheorem.identity_expansion_fixed
#print axioms MCore.Real.P02TerminalRecurrenceTheorem.terminal_recurrence_signature
#print axioms MCore.Real.P02TerminalRecurrenceTheorem.terminal_endpoint_closes_final_root

end P02TerminalRecurrenceTheorem
end Real
end MCore
