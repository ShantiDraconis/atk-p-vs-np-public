import MCore.Real.P02TotalCandidateFailureMinCut
import MCore.Real.P02SemanticNegationCounterexample

namespace MCore
namespace Real
namespace P02ExactnessKernelFinalRefutation

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02TotalCandidateFailureMinCut
open P02SemanticNegationReduction
open P02SemanticNegationCounterexample

abbrev CanonicalSAT : BitLanguage :=
  SATBits circuitBitEncoding

/-- Certified negative guard: the semantic-negation invariant route is false
and therefore cannot be reused as a positive P02 producer. -/
theorem semantic_negation_invariant_refuted :
    ¬ SEMANTIC_NEGATION_INVARIANT_OPEN_MATH :=
  semanticNegationInvariant_open_math_refuted

/-- Exact normal form already established for G2. -/
theorem mincut_exact_form :
    Nonempty TotalSemanticFailureProducer ↔
      UniversalFailure CanonicalSAT :=
  totalSemanticFailureProducer_iff_universalFailure

/-- The genuine counterobject to UniversalFailure is not another failure
producer. It is a deterministic polynomial-time realization of the same
canonical SAT language. -/
def G2RefutationWitness : Type :=
  PolyDTMRealization CanonicalSAT

/-- Any real SAT-in-P witness refutes universal failure directly on its own
candidate. -/
theorem realization_refutes_universalFailure
    (R : G2RefutationWitness) :
    ¬ UniversalFailure CanonicalSAT := by
  intro hFail
  rcases hFail R.candidate with ⟨x, hBad⟩
  exact hBad (R.decides x)

/-- By exactness, the same witness empties the total semantic failure producer
type. -/
theorem realization_refutes_totalSemanticFailure
    (R : G2RefutationWitness) :
    ¬ Nonempty TotalSemanticFailureProducer := by
  intro hProd
  have hUF : UniversalFailure CanonicalSAT :=
    mincut_exact_form.mp hProd
  exact realization_refutes_universalFailure R hUF

/-- The corrected 3/3 refutation kernel. Supplying one actual
PolyDTMRealization CanonicalSAT closes the refutation branch. -/
theorem G2_exactness_closed_by_refutation
    (R : G2RefutationWitness) :
    ¬ Nonempty TotalSemanticFailureProducer ∧
      ¬ UniversalFailure CanonicalSAT :=
  ⟨realization_refutes_totalSemanticFailure R,
   realization_refutes_universalFailure R⟩

/-- Exact accounting identity for the refutation branch:
a witness of SAT ∈ P is precisely the concrete data required by this kernel.
No failure-producer wrapper can substitute for it. -/
theorem refutationWitness_iff_sat_in_p :
    Nonempty G2RefutationWitness ↔ InP CanonicalSAT :=
  Iff.rfl

#print axioms MCore.Real.P02ExactnessKernelFinalRefutation.semantic_negation_invariant_refuted
#print axioms MCore.Real.P02ExactnessKernelFinalRefutation.mincut_exact_form
#print axioms MCore.Real.P02ExactnessKernelFinalRefutation.realization_refutes_universalFailure
#print axioms MCore.Real.P02ExactnessKernelFinalRefutation.realization_refutes_totalSemanticFailure
#print axioms MCore.Real.P02ExactnessKernelFinalRefutation.G2_exactness_closed_by_refutation
#print axioms MCore.Real.P02ExactnessKernelFinalRefutation.refutationWitness_iff_sat_in_p

end P02ExactnessKernelFinalRefutation
end Real
end MCore
