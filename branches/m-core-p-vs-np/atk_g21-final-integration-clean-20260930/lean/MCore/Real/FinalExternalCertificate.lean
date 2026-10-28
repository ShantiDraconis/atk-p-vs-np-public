import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits
import MCore.Real.G3ModelMatch

namespace MCore
namespace Real
namespace FinalExternalCertificate

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open FailProofAllGaps
open OfficialModel
open G3ModelMatch

/-- Exact three-producer payload for external promotion.

G1: concrete canonical SAT NP realization.
G2: concrete universal deterministic failure generator.
G3: explicit external-model selection, provenance, normalization and two-way
polynomial simulations. -/
structure FinalExternalInputs where
  g1 : SATInNPGap circuitBitEncoding
  g2 : FailureGenerator (SATBits circuitBitEncoding)
  g3 : G3ExternalContract

def FinalExternalInputs.toSATExternalClosure
    (I : FinalExternalInputs) :
    SATExternalClosure I.g3.selection.model.P I.g3.selection.model.NP :=
  { encoding := circuitBitEncoding
    sat_in_np := I.g1
    fail_generator := I.g2
    model_match := I.g3.toExternalModelMatch }

def FinalExternalInputs.toFinalGapCertificate
    (I : FinalExternalInputs) :
    FinalGapCertificate I.g3.selection.model.P I.g3.selection.model.NP :=
  { target := SATBits circuitBitEncoding
    target_in_np := I.g1
    fail_generator := I.g2
    model_match := I.g3.toExternalModelMatch }

theorem final_external_certificate
    (I : FinalExternalInputs) :
    OfficialPneqNP I.g3.selection.model.P I.g3.selection.model.NP := by
  exact final_gap_certificate_closes I.toFinalGapCertificate

def FinalExternalGap : Prop :=
  Nonempty FinalExternalInputs

theorem final_external_gap_closes
    (h : FinalExternalGap) :
    ∃ S : OfficialModelSelection,
      OfficialPneqNP S.model.P S.model.NP := by
  rcases h with ⟨I⟩
  exact ⟨I.g3.selection, final_external_certificate I⟩

#print axioms MCore.Real.FinalExternalCertificate.final_external_certificate
#print axioms MCore.Real.FinalExternalCertificate.final_external_gap_closes

end FinalExternalCertificate
end Real
end MCore
