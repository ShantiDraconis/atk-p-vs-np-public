import MCore.Real.RigorousTerminalDecomposition
import MCore.Real.FinalProofAttack

namespace MCore
namespace Real
namespace RigorousP02ProducerSpec

open CircuitK1
open CanonicalFinalProof
open EncodedFinalProof
open RigorousTerminalDecomposition

/--
One material counterexample against one deterministic polynomial-time
candidate in the hardened canonical-input model.

The input circuit is part of the witness.  The failure proof is about the
candidate started from the fixed canonical encoding of that circuit.
-/
structure CandidateFailureWitness
    (M : EncodedPolyDTMCandidate) : Prop where
  circuit : Circuit
  fails : ¬ M.CorrectAt SATLanguage circuit

/-- Pointwise material producer form of the exact P02 lower-bound target. -/
def CandidateFailureFamily : Prop :=
  ∀ M : EncodedPolyDTMCandidate,
    Nonempty (CandidateFailureWitness M)

/--
Computable-looking dependent producer type.  An inhabitant selects an explicit
failure witness for every candidate.  This is stronger data than merely naming
the lower-bound proposition, but classically it carries exactly the same
pointwise mathematical content.
-/
abbrev CandidateFailureProducer :=
  (M : EncodedPolyDTMCandidate) → CandidateFailureWitness M

theorem failure_family_iff_encoded_p02 :
    CandidateFailureFamily ↔ EncodedP02Target := by
  constructor
  · intro h M
    rcases h M with ⟨w⟩
    exact ⟨w.circuit, w.fails⟩
  · intro h M
    rcases h M with ⟨phi, hfail⟩
    exact ⟨⟨phi, hfail⟩⟩

/--
Classical packaging theorem: pointwise existential counterexamples can be
collected into one dependent producer.  Classical.choice packages witnesses;
it does not establish their existence.
-/
theorem producer_nonempty_iff_encoded_p02 :
    Nonempty CandidateFailureProducer ↔ EncodedP02Target := by
  constructor
  · rintro ⟨P⟩ M
    exact ⟨(P M).circuit, (P M).fails⟩
  · intro h
    have hfam : CandidateFailureFamily :=
      failure_family_iff_encoded_p02.mpr h
    classical
    refine ⟨fun M => Classical.choice (hfam M)⟩

/-- A material failure witness contradicts a claimed all-input SAT decider
whose candidate is the same machine. -/
theorem witness_refutes_realization
    (R : EncodedPolyDTMRealization SATLanguage)
    (w : CandidateFailureWitness R.candidate) :
    False :=
  w.fails (R.decides w.circuit)

/-- The exact lower-bound producer excludes every encoded SAT realization. -/
theorem producer_refutes_encoded_sat_in_p
    (P : CandidateFailureProducer) :
    EncodedSATNotInP := by
  intro hP
  rcases hP with ⟨R⟩
  exact witness_refutes_realization R (P R.candidate)

/-- The rigorous final pair cannot hide the lower-bound obligation. -/
theorem rigorous_pair_no_escape_p02
    (C : RigorousPNPFinalPair) :
    EncodedP02Target :=
  C.p02

/-- Likewise, an external rigorous final payload projects back to the exact
universal candidate-failure target. -/
theorem rigorous_external_no_escape_p02
    (E : RigorousFinalExternal) :
    EncodedP02Target :=
  E.lowerBound.fail_proof

/--
Firewall for the legacy arbitrary-encoder model.

That older SAT lower-bound target is formally refuted by its own smuggled
encoder construction.  It must never be used as the material P02 producer for
the hardened encoded model.
-/
theorem legacy_arbitrary_encode_lower_bound_uninhabited :
    ¬ SATLowerBoundCertificate :=
  FinalProofAttack.current_SATLowerBoundCertificate_refuted

/-- Exact live P02 frontier after hardening the input model. -/
def LIVE_P02_MATERIAL_TARGET : Prop :=
  CandidateFailureFamily

theorem live_p02_material_target_iff :
    LIVE_P02_MATERIAL_TARGET ↔ EncodedSATNotInP := by
  rw [failure_family_iff_encoded_p02]
  exact encoded_p02_target_iff_sat_not_in_p

#print axioms MCore.Real.RigorousP02ProducerSpec.failure_family_iff_encoded_p02
#print axioms MCore.Real.RigorousP02ProducerSpec.producer_nonempty_iff_encoded_p02
#print axioms MCore.Real.RigorousP02ProducerSpec.witness_refutes_realization
#print axioms MCore.Real.RigorousP02ProducerSpec.producer_refutes_encoded_sat_in_p
#print axioms MCore.Real.RigorousP02ProducerSpec.rigorous_pair_no_escape_p02
#print axioms MCore.Real.RigorousP02ProducerSpec.legacy_arbitrary_encode_lower_bound_uninhabited
#print axioms MCore.Real.RigorousP02ProducerSpec.live_p02_material_target_iff

end RigorousP02ProducerSpec
end Real
end MCore
