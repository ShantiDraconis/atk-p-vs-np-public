import MCore.Real.P02TerminalForcingG2

namespace MCore
namespace Real
namespace StructuralFixedPoint

open CanonicalFinalProof
open P02TerminalForcingG2

/--
A refinement is conservative when its expanded target and the terminal
proposition can be translated in both directions without additional
mathematical assumptions.
-/
structure ConservativeRefinement (P : Prop) where
  target : Prop
  sound : target → P
  complete : P → target

theorem no_escape_from_terminal
    {P : Prop}
    (R : ConservativeRefinement P) :
    R.target ↔ P :=
  ⟨R.sound, R.complete⟩

/--
A chain in which each stage is only a conservative reformulation of the
previous stage never gains terminal strength.
-/
structure ZeroGainChain (P : Prop) where
  stage : Nat → Prop
  base : stage 0 ↔ P
  step : ∀ n : Nat, stage (n + 1) ↔ stage n

theorem zero_gain_chain
    {P : Prop}
    (C : ZeroGainChain P) :
    ∀ n : Nat, C.stage n ↔ P := by
  intro n
  induction n with
  | zero =>
      exact C.base
  | succ n ih =>
      exact (C.step n).trans ih

/--
Introducing auxiliary parameters is zero-gain whenever they can both be
constructed from P and eliminated back to P.
-/
theorem existential_auxiliary_zero_gain
    {P : Prop}
    {A : Type}
    {Q : A → Prop}
    (eliminate : (∃ a, Q a) → P)
    (introduce : P → ∃ a, Q a) :
    (∃ a, Q a) ↔ P :=
  ⟨eliminate, introduce⟩

/--
Pointwise witnesses and one uniform selector carry the same classical logical
content. The selector itself contributes no lower-bound theorem.
-/
theorem pointwise_iff_uniform_selector
    {A W : Type}
    {R : A → W → Prop} :
    (∀ a : A, ∃ w : W, R a w) ↔
      ∃ F : A → W, ∀ a : A, R a (F a) := by
  constructor
  · intro h
    classical
    let F : A → W := fun a => Classical.choose (h a)
    exact ⟨F, fun a => Classical.choose_spec (h a)⟩
  · rintro ⟨F, hF⟩
    intro a
    exact ⟨F a, hF a⟩

/--
Splitting failure of a conjunction into two branches is also a conservative
classical refinement.
-/
theorem neg_and_iff_neg_or_neg
    {A B : Prop} :
    ¬ (A ∧ B) ↔ (¬ A ∨ ¬ B) := by
  classical
  constructor
  · intro h
    by_cases hA : A
    · exact Or.inr (fun hB => h ⟨hA, hB⟩)
    · exact Or.inl hA
  · intro h
    rintro ⟨hA, hB⟩
    exact h.elim (fun hnA => hnA hA) (fun hnB => hnB hB)

/--
Generic stable-mincut criterion: if every proposed next stage is conservative
over the current terminal proposition, then every such target is still exactly
the same terminal proposition.
-/
theorem stable_mincut
    {P : Prop}
    {I : Type}
    (refine : I → ConservativeRefinement P) :
    ∀ i : I, (refine i).target ↔ P := by
  intro i
  exact no_escape_from_terminal (refine i)

/--
G2 specialization of the generic pointwise/uniform-selector theorem.
This does not prove G2. It proves that changing between the two quantifier
presentations creates no mathematical gain.
-/
theorem g2_pointwise_iff_uniform :
    (∀ M : PolyDTMCandidate,
      ∃ x : BitString,
        ¬ M.CorrectAt P02TerminalForcingG2.CanonicalSAT x) ↔
    (∃ F : PolyDTMCandidate → BitString,
      ∀ M : PolyDTMCandidate,
        ¬ M.CorrectAt
          P02TerminalForcingG2.CanonicalSAT
          (F M)) := by
  exact pointwise_iff_uniform_selector

/--
The uniform side above is definitionally the exposed G2 terminal obligation.
Thus pointwise expansion followed by selector packaging returns to G2_TERMINAL.
-/
theorem g2_structural_fixed_point :
    (∀ M : PolyDTMCandidate,
      ∃ x : BitString,
        ¬ M.CorrectAt P02TerminalForcingG2.CanonicalSAT x) ↔
      P02TerminalForcingG2.G2_TERMINAL := by
  constructor
  · intro h
    rcases g2_pointwise_iff_uniform.mp h with ⟨F, hF⟩
    exact ⟨F,
      (P02TerminalForcingG2.failureLaw_iff_correctAt F).mpr hF⟩
  · rintro ⟨F, hF⟩
    have hCorrect :
        ∀ M : PolyDTMCandidate,
          ¬ M.CorrectAt
            P02TerminalForcingG2.CanonicalSAT
            (F M) :=
      (P02TerminalForcingG2.failureLaw_iff_correctAt F).mp hF
    exact g2_pointwise_iff_uniform.mpr ⟨F, hCorrect⟩

#print axioms MCore.Real.StructuralFixedPoint.no_escape_from_terminal
#print axioms MCore.Real.StructuralFixedPoint.zero_gain_chain
#print axioms MCore.Real.StructuralFixedPoint.existential_auxiliary_zero_gain
#print axioms MCore.Real.StructuralFixedPoint.pointwise_iff_uniform_selector
#print axioms MCore.Real.StructuralFixedPoint.neg_and_iff_neg_or_neg
#print axioms MCore.Real.StructuralFixedPoint.stable_mincut
#print axioms MCore.Real.StructuralFixedPoint.g2_pointwise_iff_uniform
#print axioms MCore.Real.StructuralFixedPoint.g2_structural_fixed_point

end StructuralFixedPoint
end Real
end MCore
