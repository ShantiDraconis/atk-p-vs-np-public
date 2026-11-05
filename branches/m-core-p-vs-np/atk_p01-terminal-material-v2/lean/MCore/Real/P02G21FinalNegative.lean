import MCore.Real.P02LiteralFixedPointCountermodel

namespace MCore
namespace Real
namespace P02G21FinalNegative

open CanonicalFinalProof
open P02ClockedDiagonalCompiler
open P02LiteralFixedPointCountermodel

/-- Canonical proposition for the literal two-constant fixed-point formulation
that was investigated on the G2.1 route. -/
def LiteralFixedPointFormulation : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString, semanticDiagonalBits M x = x

/-- Final negative theorem for the literal fixed-point FORMULATION.

This theorem closes only the literal fixed-point formulation.  It does not
close the semantic self-embedding replacement route and does not prove
SAT ∉ P or P ≠ NP. -/
theorem G21_literal_fixed_point_falsified :
    ¬ LiteralFixedPointFormulation := by
  exact no_universal_literal_fixed_point

/-- Abstract negative-control schema exported from any formulation
falsification.  This is the reusable A -> not A' / incompatibility shape;
the concrete target must still prove its own implication hReject. -/
theorem formulation_negative_control
    {A A' P : Prop}
    (hReject : A → ¬ A') :
    A → (¬ A' ∧ (A' ∧ P → False)) := by
  intro hA
  have hn : ¬ A' := hReject hA
  exact ⟨hn, fun h => hn h.1⟩

/-- Specialization showing that assuming the falsified literal formulation
immediately yields contradiction. -/
theorem G21_literal_fixed_point_inconsistent :
    LiteralFixedPointFormulation → False := by
  intro h
  exact G21_literal_fixed_point_falsified h

#print axioms MCore.Real.P02G21FinalNegative.G21_literal_fixed_point_falsified
#print axioms MCore.Real.P02G21FinalNegative.formulation_negative_control
#print axioms MCore.Real.P02G21FinalNegative.G21_literal_fixed_point_inconsistent

end P02G21FinalNegative
end Real
end MCore
