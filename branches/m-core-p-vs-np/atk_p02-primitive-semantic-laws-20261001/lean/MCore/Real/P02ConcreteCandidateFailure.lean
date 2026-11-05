import MCore.Real.P02SemanticAlignmentCountermodel
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P02ConcreteCandidateFailure

open CircuitK1
open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02UniversalFailureMinCut
open P02SemanticAlignmentCountermodel

/--
Concrete canonical SAT input: NOT TRUE.
Its Boolean semantics is false, so the encoded bitstring is not in canonical SAT.
-/
def notTrueCircuit : Circuit :=
  .not (.const true)

def notTrueBits : BitString :=
  encodeCircuit notTrueCircuit

theorem notTrue_not_sat :
    ¬ CanonicalSAT notTrueBits := by
  intro h
  change SATBits circuitBitEncoding (encodeCircuit notTrueCircuit) at h
  rw [encoded_sat_equivalence] at h
  change SATLanguage notTrueCircuit at h
  simpa [notTrueCircuit, SATLanguage, evalCircuit] using h

/--
The four-state discriminator accepts the concrete NOT TRUE encoding because
the second tag bit is true.
-/
theorem discriminator_accepts_notTrue :
    DeclaredAccept discriminatorCandidate notTrueBits := by
  change
    discriminatorCandidate.accepting
      (discriminatorCandidate.machine.run
        (discriminatorCandidate.timeBound notTrueBits.length)
        (initialTMConfig discriminatorCandidate.machine notTrueBits)).state =
      true
  rfl

/--
Therefore the discriminator has a concrete semantic error on NOT TRUE.
-/
theorem discriminator_not_correctAt_notTrue :
    ¬ discriminatorCandidate.CorrectAt CanonicalSAT notTrueBits := by
  intro hCorrect
  rcases hCorrect with ⟨_, hsem⟩
  have hsat : CanonicalSAT notTrueBits :=
    hsem.mp discriminator_accepts_notTrue
  exact notTrue_not_sat hsat

/--
Candidate-local negative evidence object with no universal lower-bound content.
-/
structure CandidateFailureWitness (candidate : PolyDTMCandidate) where
  input : BitString
  failure : ¬ candidate.CorrectAt CanonicalSAT input

def discriminatorFailureWitness :
    CandidateFailureWitness discriminatorCandidate where
  input := notTrueBits
  failure := discriminator_not_correctAt_notTrue

/--
A claimed full SAT realization using this exact discriminator is impossible.
-/
theorem discriminator_cannot_be_sat_realization :
    ¬ ∃ R : PolyDTMRealization CanonicalSAT,
        R.candidate = discriminatorCandidate := by
  rintro ⟨R, hR⟩
  have hgood := R.decides notTrueBits
  rw [hR] at hgood
  exact discriminator_not_correctAt_notTrue hgood

/--
Generic local incompatibility: a concrete failure witness refutes any claimed
full realization whose candidate is the same machine.
-/
theorem failureWitness_incompatible_with_realization
    {candidate : PolyDTMCandidate}
    (F : CandidateFailureWitness candidate)
    (R : PolyDTMRealization CanonicalSAT)
    (hSame : R.candidate = candidate) :
    False := by
  have hgood := R.decides F.input
  rw [hSame] at hgood
  exact F.failure hgood

#print axioms MCore.Real.P02ConcreteCandidateFailure.notTrue_not_sat
#print axioms MCore.Real.P02ConcreteCandidateFailure.discriminator_accepts_notTrue
#print axioms MCore.Real.P02ConcreteCandidateFailure.discriminator_not_correctAt_notTrue
#print axioms MCore.Real.P02ConcreteCandidateFailure.discriminator_cannot_be_sat_realization
#print axioms MCore.Real.P02ConcreteCandidateFailure.failureWitness_incompatible_with_realization

end P02ConcreteCandidateFailure
end Real
end MCore
