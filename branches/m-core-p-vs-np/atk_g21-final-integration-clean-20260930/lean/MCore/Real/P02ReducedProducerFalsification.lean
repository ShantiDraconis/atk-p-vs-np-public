import MCore.Real.P02FinalProofProducer
import MCore.Real.P02LiteralFixedPointCountermodel

namespace MCore
namespace Real
namespace P02ReducedProducerFalsification

open CanonicalFinalProof
open P02KleeneBridge
open P02FinalProofProducer
open P02LiteralFixedPointCountermodel
open P02ClockedDiagonalCompiler

/-- A ReducedProducer would manufacture a literal semanticDiagonalBits fixed
point for every candidate by applying the existing Kleene theorem to its
compiler. -/
theorem reducedProducer_implies_universal_literal_fixed_point
    (R : ReducedProducer) :
    ∀ M : PolyDTMCandidate,
      ∃ x : BitString, semanticDiagonalBits M x = x := by
  intro M
  let c := Classical.choose (kleene_fixed_point (R.compiler M))
  have hfixed :
      Nat.Partrec.Code.eval c = (R.compiler M).f c :=
    Classical.choose_spec (kleene_fixed_point (R.compiler M))
  let x := R.selfInput M c
  refine ⟨x, ?_⟩
  exact (R.same_input_of_fixed M c hfixed).symm

/-- The reduced semantic-fixed-point producer is therefore impossible. -/
theorem not_ReducedProducer :
    ¬ Nonempty ReducedProducer := by
  rintro ⟨R⟩
  exact no_universal_literal_fixed_point
    (reducedProducer_implies_universal_literal_fixed_point R)

#print axioms MCore.Real.P02ReducedProducerFalsification.reducedProducer_implies_universal_literal_fixed_point
#print axioms MCore.Real.P02ReducedProducerFalsification.not_ReducedProducer

end P02ReducedProducerFalsification
end Real
end MCore
