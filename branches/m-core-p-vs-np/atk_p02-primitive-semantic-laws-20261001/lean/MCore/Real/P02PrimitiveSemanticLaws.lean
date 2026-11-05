import MCore.Real.P02SemanticTransformerCore

namespace MCore
namespace Real
namespace P02PrimitiveSemanticLaws

open CircuitK1
open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02SemanticTransformerCore

/--
The concrete semantic-negation transformer has a two-point image:
it emits exactly the canonical constant-false or constant-true circuit encoding.
No fixed-point or lower-bound hypothesis is involved.
-/
theorem semanticNegationBits_two_point_range
    (M : PolyDTMCandidate)
    (x : BitString) :
    semanticNegationBits M x = encodeCircuit (.const false) ∨
    semanticNegationBits M x = encodeCircuit (.const true) := by
  unfold semanticNegationBits semanticNegationCircuit
  cases h : declaredAcceptBit M x <;>
    simp [h]

/--
Every transformed output has exact length 3.
-/
theorem semanticNegationBits_length_three
    (M : PolyDTMCandidate)
    (x : BitString) :
    (semanticNegationBits M x).length = 3 :=
  semanticNegationBits_length M x

/--
Any literal string fixed point of this transformer is forced into the
two-element image above.  In particular, any such fixed point has length 3.
-/
theorem fixed_point_is_constant_encoding
    (M : PolyDTMCandidate)
    (x : BitString)
    (hfix : semanticNegationBits M x = x) :
    x = encodeCircuit (.const false) ∨
    x = encodeCircuit (.const true) := by
  rcases semanticNegationBits_two_point_range M x with h | h
  · exact Or.inl hfix ▸ h
  · exact Or.inr hfix ▸ h

theorem fixed_point_length_three
    (M : PolyDTMCandidate)
    (x : BitString)
    (hfix : semanticNegationBits M x = x) :
    x.length = 3 := by
  rw [← hfix]
  exact semanticNegationBits_length_three M x

/--
If the candidate agrees with ordinary Boolean semantics on the two constant
circuit encodings, then the concrete negation transformer has no literal
string fixed point.

This is a finite semantic statement about two concrete strings, not an
OpenMath or P-vs-NP hypothesis.
-/
theorem no_fixed_point_of_constant_semantics
    (M : PolyDTMCandidate)
    (hFalse :
      ¬ DeclaredAccept M (encodeCircuit (.const false)))
    (hTrue :
      DeclaredAccept M (encodeCircuit (.const true))) :
    ∀ x : BitString, semanticNegationBits M x ≠ x := by
  intro x hfix
  rcases fixed_point_is_constant_encoding M x hfix with hxFalse | hxTrue
  · subst x
    have hflip :=
      semanticNegationBits_flip M (encodeCircuit (.const false))
    have hsat :
        SATTarget (semanticNegationBits M (encodeCircuit (.const false))) := by
      apply hflip.mpr
      exact hFalse
    have hself :
        semanticNegationBits M (encodeCircuit (.const false)) =
          encodeCircuit (.const false) := hfix
    rw [hself] at hsat
    change SATLanguage (.const false) at hsat
    simpa [SATLanguage, evalCircuit] using hsat
  · subst x
    have hflip :=
      semanticNegationBits_flip M (encodeCircuit (.const true))
    have hnotSat :
        ¬ SATTarget (semanticNegationBits M (encodeCircuit (.const true))) := by
      intro hsat
      exact (hflip.mp hsat) hTrue
    have hself :
        semanticNegationBits M (encodeCircuit (.const true)) =
          encodeCircuit (.const true) := hfix
    apply hnotSat
    rw [hself]
    change SATLanguage (.const true)
    simp [SATLanguage, evalCircuit]

/--
The four-state discriminator from the countermodel satisfies the two finite
constant-semantics facts, so the absence of literal fixed points follows from
the primitive two-point theorem.
-/
theorem discriminator_has_no_literal_fixed_point :
    ∀ x : BitString,
      semanticNegationBits
        P02SemanticAlignmentCountermodel.discriminatorCandidate x ≠ x := by
  apply no_fixed_point_of_constant_semantics
  · exact
      P02SemanticAlignmentCountermodel.discriminator_rejects_constFalse
  · exact
      P02SemanticAlignmentCountermodel.discriminator_accepts_constTrue

#print axioms MCore.Real.P02PrimitiveSemanticLaws.semanticNegationBits_two_point_range
#print axioms MCore.Real.P02PrimitiveSemanticLaws.fixed_point_is_constant_encoding
#print axioms MCore.Real.P02PrimitiveSemanticLaws.no_fixed_point_of_constant_semantics
#print axioms MCore.Real.P02PrimitiveSemanticLaws.discriminator_has_no_literal_fixed_point

end P02PrimitiveSemanticLaws
end Real
end MCore
