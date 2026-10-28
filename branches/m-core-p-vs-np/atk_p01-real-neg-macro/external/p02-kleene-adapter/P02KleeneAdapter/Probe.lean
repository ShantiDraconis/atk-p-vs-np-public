import Mathlib.Computability.PartrecCode

namespace P02KleeneAdapter

open Nat.Partrec

/-- Upstream Roger fixed-point theorem is available at the pinned Mathlib. -/
theorem roger_fixed_point_probe
    {f : Code → Code}
    (hf : Computable f) :
    ∃ c : Code, Code.eval (f c) = Code.eval c :=
  Code.fixed_point hf

/-- Upstream Kleene second recursion theorem is available at the pinned Mathlib. -/
theorem kleene_second_recursion_probe
    {f : Code → ℕ →. ℕ}
    (hf : Partrec₂ f) :
    ∃ c : Code, Code.eval c = f c :=
  Code.fixed_point₂ hf

#print axioms P02KleeneAdapter.roger_fixed_point_probe
#print axioms P02KleeneAdapter.kleene_second_recursion_probe

end P02KleeneAdapter
