import MCore.Real.P01ConstructionClose
import MCore.Real.P02G21G22Attack
import MCore.Real.FinalExternalTwoGap
import MCore.Real.FinalExternalCertificate
import MCore.Real.P012FailClosed
import MCore.Real.TerminalGapP012

namespace MCore
namespace Real
namespace FinalProofRecoveryChain

open CanonicalFinalProof
open P01FinalCertificate
open P02G21G22Attack
open FinalExternalTwoGap
open FinalExternalCertificate
open OfficialModel

/-- Canonical terminal delta of the recovered P-vs-NP chain. -/
abbrev TerminalDelta : Prop :=
  P01ConstructionGap ∧ G21Pointwise

/-- No additional mathematical producer is required after the two terminal
producers: the certified FinalExternal reduction consumes them directly. -/
theorem terminal_delta_closes_external
    (h : TerminalDelta) :
    ∃ S : OfficialModelSelection,
      OfficialPneqNP S.model.P S.model.NP := by
  exact final_external_two_gap_closes h

/-- The recovered chain is definitionally the certified two-gap boundary. -/
theorem terminal_delta_iff_final_external_two_gap :
    TerminalDelta ↔ FinalExternalTwoGap := by
  rfl

#print axioms MCore.Real.FinalProofRecoveryChain.terminal_delta_closes_external
theorem terminal_delta_iff_p012_rigid_core :
    TerminalDelta ↔ P012FailClosed.RigidCore := by
  rfl

theorem terminal_delta_iff_terminal_gap_p012 :
    TerminalDelta ↔
      (P01FinalCertificate.P01ConstructionGap ∧
       P02G21G22Attack.G21Pointwise) := by
  rfl

#print axioms MCore.Real.FinalProofRecoveryChain.terminal_delta_iff_terminal_gap_p012

#print axioms MCore.Real.FinalProofRecoveryChain.terminal_delta_iff_p012_rigid_core

#print axioms MCore.Real.FinalProofRecoveryChain.terminal_delta_iff_final_external_two_gap

end FinalProofRecoveryChain
end Real
end MCore
