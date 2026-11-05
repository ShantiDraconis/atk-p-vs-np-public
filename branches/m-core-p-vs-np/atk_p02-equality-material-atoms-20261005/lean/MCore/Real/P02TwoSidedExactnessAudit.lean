import MCore.Real.P02ExactnessKernelFinalRefutation
import MCore.Real.P01RawTotalizationProducer
import MCore.Real.CanonicalPSubsetNP

namespace MCore
namespace Real
namespace P02TwoSidedExactnessAudit

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open CanonicalPSubsetNP
open P02ExactnessKernelFinalRefutation

abbrev CanonicalSAT : BitLanguage :=
  SATBits circuitBitEncoding

/-- P01 supplies SAT in NP for the same canonical encoding. -/
theorem canonicalSAT_inNP :
    InNP CanonicalSAT := by
  exact P01FinalCertificate.construction_closes_p01
    P01RawTotalizationProducer.p01ConstructionGap_closed

/-- Equality-side bridge: SAT in P must transfer every NP language into P.
This is the Cook--Levin/composition content; it is not contained in G2. -/
structure CanonicalSATCompletenessTransfer where
  np_to_p_of_sat_in_p :
    InP CanonicalSAT →
      ∀ L : BitLanguage, InNP L → InP L

/-- Given the equality-side transfer, SAT in P yields extensional P = NP
inside the canonical model. -/
theorem sat_in_p_implies_p_eq_np
    (T : CanonicalSATCompletenessTransfer)
    (hSAT : InP CanonicalSAT) :
    ∀ L : BitLanguage, InP L ↔ InNP L := by
  intro L
  constructor
  · exact inP_subset_inNP L
  · exact T.np_to_p_of_sat_in_p hSAT L

/-- SAT not in P closes the separation side directly from the certified
SAT-in-NP witness. -/
theorem sat_not_in_p_implies_p_ne_np
    (hNotP : ¬ InP CanonicalSAT) :
    PneqNP := by
  have hFail : UniversalFailure CanonicalSAT :=
    not_in_p_implies_universal_failure hNotP
  exact target_failure_implies_p_ne_np canonicalSAT_inNP hFail

/-- Exact two-sided orientation once the equality-side completeness transfer
is supplied. The G2 dichotomy itself is classical; only the equality branch
needs the additional transfer. -/
inductive FinalOrientation
    (T : CanonicalSATCompletenessTransfer) : Type where
  | separation (h : PneqNP)
  | equality (h : ∀ L : BitLanguage, InP L ↔ InNP L)

theorem orient_from_canonicalSAT
    (T : CanonicalSATCompletenessTransfer) :
    Nonempty (FinalOrientation T) := by
  classical
  by_cases hSAT : InP CanonicalSAT
  · exact ⟨.equality (sat_in_p_implies_p_eq_np T hSAT)⟩
  · exact ⟨.separation (sat_not_in_p_implies_p_ne_np hSAT)⟩

/-- Refutation witness for G2 is exactly SAT in P, but this theorem deliberately
does not promote SAT in P to P = NP without CanonicalSATCompletenessTransfer. -/
theorem g2_refutation_witness_iff_sat_in_p :
    Nonempty G2RefutationWitness ↔ InP CanonicalSAT :=
  refutationWitness_iff_sat_in_p

/-- Proving G2 itself gives the separation endpoint immediately. -/
theorem g2_proved_implies_p_ne_np
    (hG2 : UniversalFailure CanonicalSAT) :
    PneqNP :=
  target_failure_implies_p_ne_np canonicalSAT_inNP hG2

#print axioms MCore.Real.P02TwoSidedExactnessAudit.canonicalSAT_inNP
#print axioms MCore.Real.P02TwoSidedExactnessAudit.sat_in_p_implies_p_eq_np
#print axioms MCore.Real.P02TwoSidedExactnessAudit.sat_not_in_p_implies_p_ne_np
#print axioms MCore.Real.P02TwoSidedExactnessAudit.orient_from_canonicalSAT
#print axioms MCore.Real.P02TwoSidedExactnessAudit.g2_refutation_witness_iff_sat_in_p
#print axioms MCore.Real.P02TwoSidedExactnessAudit.g2_proved_implies_p_ne_np

end P02TwoSidedExactnessAudit
end Real
end MCore
