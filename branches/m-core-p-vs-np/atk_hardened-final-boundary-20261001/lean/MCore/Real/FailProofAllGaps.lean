import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace FailProofAllGaps

open CanonicalFinalProof

/-- A Skolemized fail proof: one explicit counterexample input for every
    deterministic polynomial-time candidate. -/
structure FailureGenerator (language : BitLanguage) where
  counterexample : PolyDTMCandidate → BitString
  fails :
    ∀ candidate : PolyDTMCandidate,
      ¬ candidate.CorrectAt language (counterexample candidate)

theorem failure_generator_implies_universal_failure
    {language : BitLanguage}
    (G : FailureGenerator language) :
    UniversalFailure language := by
  intro candidate
  exact ⟨G.counterexample candidate, G.fails candidate⟩

noncomputable def failureGeneratorOfUniversalFailure
    {language : BitLanguage}
    (h : UniversalFailure language) :
    FailureGenerator language := by
  classical
  let chooseInput : PolyDTMCandidate → BitString :=
    fun candidate => Classical.choose (h candidate)
  refine
    { counterexample := chooseInput
      fails := ?_ }
  intro candidate
  exact Classical.choose_spec (h candidate)

theorem failure_generator_iff_universal_failure
    {language : BitLanguage} :
    Nonempty (FailureGenerator language) ↔ UniversalFailure language := by
  constructor
  · rintro ⟨G⟩
    exact failure_generator_implies_universal_failure G
  · intro h
    exact ⟨failureGeneratorOfUniversalFailure h⟩

/-- External/official predicates on the same bit-language universe.
    This structure states only semantic equivalence of class membership. -/
structure ExternalModelMatch
    (officialP officialNP : BitLanguage → Prop) where
  p_match : ∀ language, InP language ↔ officialP language
  np_match : ∀ language, InNP language ↔ officialNP language

def OfficialPneqNP
    (officialP officialNP : BitLanguage → Prop) : Prop :=
  ¬ ∀ language : BitLanguage, officialP language ↔ officialNP language

theorem internal_separation_transfers
    {officialP officialNP : BitLanguage → Prop}
    (hMatch : ExternalModelMatch officialP officialNP)
    (hInternal : PneqNP) :
    OfficialPneqNP officialP officialNP := by
  intro hEq
  apply hInternal
  intro language
  constructor
  · intro hP
    have hOfficialP := (hMatch.p_match language).mp hP
    have hOfficialNP := (hEq language).mp hOfficialP
    exact (hMatch.np_match language).mpr hOfficialNP
  · intro hNP
    have hOfficialNP := (hMatch.np_match language).mp hNP
    have hOfficialP := (hEq language).mpr hOfficialNP
    exact (hMatch.p_match language).mpr hOfficialP

/-- Exact three-gap payload:
    G1: one explicit NP target;
    G2: a universal fail generator for every deterministic poly-time candidate;
    G3: equivalence of the hardened internal model with the chosen external model. -/
structure FinalGapCertificate
    (officialP officialNP : BitLanguage → Prop) where
  target : BitLanguage
  target_in_np : InNP target
  fail_generator : FailureGenerator target
  model_match : ExternalModelMatch officialP officialNP

theorem final_gap_certificate_closes
    {officialP officialNP : BitLanguage → Prop}
    (cert : FinalGapCertificate officialP officialNP) :
    OfficialPneqNP officialP officialNP := by
  have hFail : UniversalFailure cert.target :=
    failure_generator_implies_universal_failure cert.fail_generator
  have hInternal : PneqNP :=
    target_failure_implies_p_ne_np cert.target_in_np hFail
  exact internal_separation_transfers cert.model_match hInternal

/-- If the external predicates are chosen to be the hardened internal model
    itself, only G1+G2 remain. -/
def InternalModelMatch :
    ExternalModelMatch InP InNP :=
  { p_match := fun _ => Iff.rfl
    np_match := fun _ => Iff.rfl }

#print axioms MCore.Real.FailProofAllGaps.failure_generator_implies_universal_failure
#print axioms MCore.Real.FailProofAllGaps.failureGeneratorOfUniversalFailure
#print axioms MCore.Real.FailProofAllGaps.failure_generator_iff_universal_failure
#print axioms MCore.Real.FailProofAllGaps.internal_separation_transfers
#print axioms MCore.Real.FailProofAllGaps.final_gap_certificate_closes

end FailProofAllGaps
end Real
end MCore
