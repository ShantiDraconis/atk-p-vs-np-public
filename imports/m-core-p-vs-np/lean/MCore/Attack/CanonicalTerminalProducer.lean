import MCore.Real.CanonicalComplexityBridge
import MCore.BackwardAudit.OrientedWitnessBoundary

namespace MCore
namespace Attack

/-- Exact fixed official-model witness target for the canonical bit-language model. -/
structure CanonicalNotInPWitness where
  language : Real.CanonicalFinalProof.BitLanguage
  in_np : Real.CanonicalComplexityBridge.canonicalInterface.inNP language
  not_in_p : ¬ Real.CanonicalComplexityBridge.canonicalInterface.inP language

/-- The canonical interface already matches the repository's official InP/InNP predicates by rfl. -/
theorem canonicalModelMatch :
    ∀ L : Real.CanonicalFinalProof.BitLanguage,
      (Real.CanonicalComplexityBridge.canonicalInterface.inP L ↔
        Real.CanonicalFinalProof.InP L) ∧
      (Real.CanonicalComplexityBridge.canonicalInterface.inNP L ↔
        Real.CanonicalFinalProof.InNP L) := by
  intro L
  exact ⟨
    Real.CanonicalComplexityBridge.canonical_interface_p_match L,
    Real.CanonicalComplexityBridge.canonical_interface_np_match L
  ⟩

/-- A genuine fixed not-in-P witness is exactly enough for the separation lane. -/
theorem canonicalWitness_closes_separation
    (w : CanonicalNotInPWitness) :
    ClosedDiscriminant.SeparationFinal
      Real.CanonicalComplexityBridge.canonicalInterface.inP
      Real.CanonicalComplexityBridge.canonicalInterface.inNP := by
  exact BackwardAudit.typeB_closes_separation
    { language := w.language
      in_np := w.in_np
      not_in_p := w.not_in_p }

def terminalProducerStatus : String :=
  "OPEN_MATH: construct CanonicalNotInPWitness; canonical model matching is already PROVED/REUSE"

#print axioms canonicalModelMatch
#print axioms canonicalWitness_closes_separation

end Attack
end MCore
