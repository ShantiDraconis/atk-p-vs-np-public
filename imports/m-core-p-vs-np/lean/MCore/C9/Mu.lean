import MCore.C9.Vars

namespace MCore
namespace C9

/-- L1: inherited C8 monotonicity. -/
theorem L1_mu_monotone (ρ : CircuitK1.Restriction) (t : FormulaTree) :
    mu (D ρ t) ≤ mu t := by
  simpa [mu, D] using CircuitC8.potential_restrictedSimplified_le ρ t

/-- L2: exact additive accounting. `delta` is defined, never postulated. -/
theorem L2_additive (ρ : CircuitK1.Restriction) (t : FormulaTree) :
    mu (D ρ t) + delta ρ t = mu t := by
  simpa [mu, D, delta, CircuitC3.drop] using CircuitC8.restricted_potential_add_drop ρ t

/-- Zero drop is exact equality, not truncated-subtraction masking. -/
theorem delta_eq_zero_iff (ρ : CircuitK1.Restriction) (t : FormulaTree) :
    delta ρ t = 0 ↔ mu (D ρ t) = mu t := by
  simpa [mu, D, delta, CircuitC3.drop] using CircuitC8.drop_eq_zero_iff ρ t

/-- Positive C9 decrement is exactly C3 strict structural descent. -/
theorem delta_pos_iff_strict (ρ : CircuitK1.Restriction) (t : FormulaTree) :
    0 < delta ρ t ↔ CircuitC3.StrictDrop ρ t := by
  simpa [mu, D, delta, CircuitC3.drop] using CircuitC8.drop_pos_iff_strict ρ t

end C9
end MCore
