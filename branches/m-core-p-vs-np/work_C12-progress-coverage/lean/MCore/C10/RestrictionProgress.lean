import MCore.C9.Step

namespace MCore
namespace C10

open C9 CircuitC8 CircuitK1 CircuitC2 CircuitC3

/-- A restriction gives structural recurrence progress when it does not increase
the syntactic variable count and either strictly lowers that count or has a
strictly positive certified structural decrement. -/
def RestrictionProgress (ρ : Restriction) (t : FormulaTree) : Prop :=
  vars (D ρ t) ≤ vars t ∧
    (vars (D ρ t) < vars t ∨ 0 < delta ρ t)

/-- C10 removes the need to supply an already-packaged C9 `ProgressStep`.
The remaining hypotheses are exactly the two observable restriction properties:
variable-count nonincrease and strict progress in variables or certified
potential decrement. -/
theorem stateRank_D_decreases_of_restriction_progress
    (ρ : Restriction) (t : FormulaTree)
    (h : RestrictionProgress ρ t) :
    stateRank (D ρ t) < stateRank t := by
  rcases h with ⟨hvars, hprogress⟩
  let v0 := vars t
  let v1 := vars (D ρ t)
  let m0 := mu t
  let m1 := mu (D ρ t)
  change recurrenceRank v1 m1 < recurrenceRank v0 m0
  have hvars' : v1 ≤ v0 := by
    exact hvars
  have hmu_le : m1 ≤ m0 := by
    exact L1_mu_monotone ρ t
  rcases hprogress with hv | hd
  · have hv' : v1 < v0 := by
      exact hv
    let fixedVars := v0 - v1
    have hfix : 0 < fixedVars := by
      dsimp [fixedVars]
      omega
    have hfixle : fixedVars ≤ v0 := by
      dsimp [fixedVars]
      omega
    have hvarseq : v1 = v0 - fixedVars := by
      dsimp [fixedVars]
      omega
    rw [hvarseq]
    exact rank_decreases_when_variable_fixed
      v0 m0 fixedVars m1 hfix hfixle hmu_le
  · by_cases hv' : v1 < v0
    · let fixedVars := v0 - v1
      have hfix : 0 < fixedVars := by
        dsimp [fixedVars]
        omega
      have hfixle : fixedVars ≤ v0 := by
        dsimp [fixedVars]
        omega
      have hvarseq : v1 = v0 - fixedVars := by
        dsimp [fixedVars]
        omega
      rw [hvarseq]
      exact rank_decreases_when_variable_fixed
        v0 m0 fixedVars m1 hfix hfixle hmu_le
    · have hvarseq : v1 = v0 := by omega
      have hadd : m1 + delta ρ t = m0 := by
        exact L2_additive ρ t
      have hmu : m1 < m0 := by omega
      rw [hvarseq]
      exact rank_decreases_when_potential_drops v0 m0 m1 hmu

/-- The certified C2 reducible example is a concrete C10 progress instance:
fixing input 0 reduces the distinct syntactic variable count. -/
theorem reducibleExample_restriction_progress :
    RestrictionProgress fixesZeroTrue reducibleExample := by
  constructor
  · decide
  · left
    decide

theorem reducibleExample_stateRank_decreases :
    stateRank (D fixesZeroTrue reducibleExample) < stateRank reducibleExample :=
  stateRank_D_decreases_of_restriction_progress
    fixesZeroTrue reducibleExample reducibleExample_restriction_progress

/-- Exact next bridge: prove this for the actual restriction family before any
universal recurrence claim is promoted. It is a proposition, not an axiom. -/
def VarsNonincreaseObligation : Prop :=
  ∀ (ρ : Restriction) (t : FormulaTree), vars (D ρ t) ≤ vars t

/-- A coverage obligation for nonconstant syntactic inputs. This is deliberately
kept separate from runtime or classical-complexity claims. -/
def ProgressCoverageObligation : Prop :=
  ∀ t : FormulaTree, 0 < vars t →
    ∃ ρ : Restriction, RestrictionProgress ρ t

/-- C10 remains epistemically downstream of the frozen C9 firewall. -/
theorem c10_classical_endpoint_not_promoted :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  C9.c9_classical_endpoint_not_promoted

theorem c10_k10_not_promoted :
    ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  C9.c9_k10_not_promoted

end C10
end MCore
