import MCore.C9.RestrictionMass

namespace MCore
namespace C9

/-- Universal C9 two-channel bridge. The left channel alone is sufficient on Good0. -/
theorem C9_TWO_CHANNEL_BRIDGE {t : FormulaTree} {ρ : CircuitK1.Restriction}
    (h : Good0 t ρ) : 0 < deltaN ρ t ∨ 0 < delta ρ t :=
  good0_two_channel_progress h

theorem GOOD0_STRICT_VAR_DESCENT {t : FormulaTree} {ρ : CircuitK1.Restriction}
    (h : Good0 t ρ) : vars (D ρ t) < vars t :=
  good0_vars_strict h

theorem REFUTED_SINGLE_CHANNEL :
    Good0 (.input 0) fixesZeroFalse ∧
    delta fixesZeroFalse (.input 0) = 0 ∧
    deltaN fixesZeroFalse (.input 0) = 1 :=
  single_channel_counterexample

/-- Epistemic firewall: C9 bridge is not a P≠NP certificate. -/
theorem c9_endpoint_not_promoted :
    ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  CircuitC8.c8_k10_not_promoted

end C9
end MCore
