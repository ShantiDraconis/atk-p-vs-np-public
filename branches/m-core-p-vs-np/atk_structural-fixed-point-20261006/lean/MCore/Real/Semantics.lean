import MCore.Real.CNFStructure

namespace MCore
namespace Real

open CircuitK1

/-- Total Boolean assignment for the existing Circuit input variables. -/
abbrev Assignment := Nat → Bool

/-- Boolean semantics of the existing Circuit AST. -/
def evalCircuit (σ : Assignment) : Circuit → Bool
  | .input i => σ i
  | .const b => b
  | .not c => !(evalCircuit σ c)
  | .and a b => Bool.and (evalCircuit σ a) (evalCircuit σ b)
  | .or a b => Bool.or (evalCircuit σ a) (evalCircuit σ b)

/-- Two existing Circuit terms are semantically equivalent under every assignment. -/
def SemanticallyEquivalent (a b : Circuit) : Prop :=
  ∀ σ : Assignment, evalCircuit σ a = evalCircuit σ b

/-- A string semantically represents φ when the frozen parser accepts it as
    some Circuit ψ and ψ has the same Boolean semantics as φ. -/
def SemanticallyRepresents (s : String) (φ : Circuit) : Prop :=
  ∃ ψ : Circuit,
    parseCNF s = some ψ ∧
    SemanticallyEquivalent ψ φ

theorem semanticallyEquivalent_refl (φ : Circuit) :
    SemanticallyEquivalent φ φ := by
  intro σ
  rfl

/-- Exact parser success is sufficient for semantic representation. -/
theorem semanticallyRepresents_of_parse_eq
    {s : String} {φ : Circuit}
    (hparse : parseCNF s = some φ) :
    SemanticallyRepresents s φ := by
  exact ⟨φ, hparse, semanticallyEquivalent_refl φ⟩

/-- Semantic representation never hides parser acceptance. -/
theorem semanticallyRepresents_has_parse
    {s : String} {φ : Circuit}
    (h : SemanticallyRepresents s φ) :
    ∃ ψ : Circuit, parseCNF s = some ψ := by
  rcases h with ⟨ψ, hparse, _⟩
  exact ⟨ψ, hparse⟩

/-- Parsed representatives preserve truth values for every assignment. -/
theorem semanticallyRepresents_eval
    {s : String} {φ : Circuit}
    (h : SemanticallyRepresents s φ)
    (σ : Assignment) :
    ∃ ψ : Circuit,
      parseCNF s = some ψ ∧
      evalCircuit σ ψ = evalCircuit σ φ := by
  rcases h with ⟨ψ, hparse, hsem⟩
  exact ⟨ψ, hparse, hsem σ⟩

#print axioms MCore.Real.semanticallyEquivalent_refl
#print axioms MCore.Real.semanticallyRepresents_of_parse_eq
#print axioms MCore.Real.semanticallyRepresents_has_parse
#print axioms MCore.Real.semanticallyRepresents_eval

end Real
end MCore
