import MCore.Real.HardenedFinalExternal
import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace HardenedFinalBoundary

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open FailProofAllGaps
open P01FinalCertificate
open HardenedFinal

/-- Exact two-producer boundary for the hardened canonical bitstring model. -/
def FINAL_TWO_PRODUCER_RESIDUAL : Prop :=
  P01ConstructionGap ∧ SATFailGap circuitBitEncoding

/-- The external payload is exactly the two material producers: P01 and the
same-language deterministic failure generator. -/
theorem final_external_nonempty_iff_two_producers :
    Nonempty HardenedFinal.FinalExternalCertificate ↔
      FINAL_TWO_PRODUCER_RESIDUAL := by
  constructor
  · rintro ⟨E⟩
    exact ⟨E.p01, ⟨E.fail⟩⟩
  · rintro ⟨hP01, ⟨G⟩⟩
    exact ⟨{
      p01 := hP01
      fail := G
    }⟩

/-- Pointwise existential form of the exact P02 material obligation. -/
def CANONICAL_P02_UNIVERSAL_FAILURE : Prop :=
  UniversalFailure (SATBits circuitBitEncoding)

theorem p02_failure_generator_iff_universal_failure :
    SATFailGap circuitBitEncoding ↔ CANONICAL_P02_UNIVERSAL_FAILURE := by
  exact failure_generator_iff_universal_failure

/-- Therefore the final external payload is also exactly P01 plus universal
failure in the same fixed finite-control canonical-input model. -/
theorem final_external_nonempty_iff_p01_and_universal_failure :
    Nonempty HardenedFinal.FinalExternalCertificate ↔
      P01ConstructionGap ∧ CANONICAL_P02_UNIVERSAL_FAILURE := by
  rw [final_external_nonempty_iff_two_producers]
  unfold FINAL_TWO_PRODUCER_RESIDUAL
  constructor
  · rintro ⟨hP01, hFailGen⟩
    exact ⟨hP01,
      p02_failure_generator_iff_universal_failure.mp hFailGen⟩
  · rintro ⟨hP01, hFail⟩
    exact ⟨hP01,
      p02_failure_generator_iff_universal_failure.mpr hFail⟩

/-- No-escape projection: every hardened external certificate contains the
actual P01 machine construction inhabitant. -/
theorem final_external_no_escape_p01
    (E : HardenedFinal.FinalExternalCertificate) :
    P01ConstructionGap :=
  E.p01

/-- No-escape projection: every hardened external certificate contains an
explicit failure generator for the same canonical SAT bit-language. -/
theorem final_external_no_escape_p02
    (E : HardenedFinal.FinalExternalCertificate) :
    FailureGenerator (SATBits circuitBitEncoding) :=
  E.fail

/-- The P02 field yields the genuine universal candidate-failure theorem. -/
theorem final_external_yields_universal_failure
    (E : HardenedFinal.FinalExternalCertificate) :
    CANONICAL_P02_UNIVERSAL_FAILURE :=
  failure_generator_implies_universal_failure E.fail

/-- If both exact material producers are supplied, the hardened root follows
with no additional mathematical hypothesis. -/
theorem exact_two_producers_to_final_root
    (hP01 : P01ConstructionGap)
    (G : FailureGenerator (SATBits circuitBitEncoding)) :
    HardenedFinal.FINAL_ROOT :=
  HardenedFinal.finalExternal_to_FINAL_ROOT
    { p01 := hP01
      fail := G }

/-- Official/external promotion remains a separate model-match layer. -/
theorem exact_two_producers_to_official_root
    {officialP officialNP : BitLanguage → Prop}
    (hP01 : P01ConstructionGap)
    (G : FailureGenerator (SATBits circuitBitEncoding))
    (hMatch : ExternalModelMatch officialP officialNP) :
    HardenedFinal.OFFICIAL_FINAL_ROOT officialP officialNP := by
  exact HardenedFinal.officialFinalExternal_to_root
    { p01 := hP01
      fail := G
      model_match := hMatch }

/-- Fixed-model internal issuance needs no extra model-match producer. -/
def internal_certificate_of_two_producers
    (hP01 : P01ConstructionGap)
    (G : FailureGenerator (SATBits circuitBitEncoding)) :
    HardenedFinal.OfficialFinalExternalCertificate InP InNP :=
  HardenedFinal.internalOfficialCertificate
    { p01 := hP01
      fail := G }

#print axioms MCore.Real.HardenedFinalBoundary.final_external_nonempty_iff_two_producers
#print axioms MCore.Real.HardenedFinalBoundary.p02_failure_generator_iff_universal_failure
#print axioms MCore.Real.HardenedFinalBoundary.final_external_nonempty_iff_p01_and_universal_failure
#print axioms MCore.Real.HardenedFinalBoundary.final_external_no_escape_p01
#print axioms MCore.Real.HardenedFinalBoundary.final_external_no_escape_p02
#print axioms MCore.Real.HardenedFinalBoundary.exact_two_producers_to_final_root
#print axioms MCore.Real.HardenedFinalBoundary.exact_two_producers_to_official_root

end HardenedFinalBoundary
end Real
end MCore
