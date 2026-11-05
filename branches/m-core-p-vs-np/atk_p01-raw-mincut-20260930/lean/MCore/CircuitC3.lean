import MCore.CircuitC2

namespace MCore
namespace CircuitC3

open CircuitK1 CircuitC2

abbrev potential (c : Circuit) : Nat := μ c

def drop (ρ : Restriction) (c : Circuit) : Nat :=
  potential c - potential (restrictedSimplified ρ c)

def StrictDrop (ρ : Restriction) (c : Circuit) : Prop :=
  potential (restrictedSimplified ρ c) < potential c

/-- Concrete strict-potential-drop witness, reduced definitionally instead of
requesting a Decidable instance for a proposition containing a function. -/
theorem reducibleExample_strict_potential_drop :
    StrictDrop fixesZeroTrue reducibleExample := by
  simp [StrictDrop, potential, restrictedSimplified, reducibleExample,
    fixesZeroTrue, restrict, simplify, μ, size, depth]

/-- Exact audited value: initial μ is 4 and residual input μ is 1. -/
@[simp] theorem reducibleExample_drop_exact :
    drop fixesZeroTrue reducibleExample = 3 := by
  simp [drop, potential, restrictedSimplified, reducibleExample,
    fixesZeroTrue, restrict, simplify, μ, size, depth]

@[simp] theorem free_oneInput_drop_zero :
    drop leavesZeroFree oneInput = 0 := by
  simp [drop, potential, restrictedSimplified, leavesZeroFree, oneInput,
    restrict, simplify, μ, size, depth]

theorem not_every_restriction_strictly_drops :
    ¬ (∀ (ρ : Restriction) (c : Circuit), StrictDrop ρ c) := by
  intro h
  have hs := h leavesZeroFree oneInput
  simp [StrictDrop, potential, restrictedSimplified, simplify, restrict, μ, size, depth,
    leavesZeroFree, oneInput] at hs

theorem c3_classical_endpoint_not_promoted : ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c2_classical_endpoint_not_promoted

theorem c3_k10_not_promoted : ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c2_k10_not_promoted

end CircuitC3
end MCore
