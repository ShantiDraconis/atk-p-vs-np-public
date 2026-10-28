import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace PNPHabitant

open CanonicalFinalProof

/-- The unique material inhabitant for the F2 separation route.

PolyDTMCandidate already carries an arbitrary polynomial time bound
coefficient * (n+1)^exponent, so quantifying over all candidates subsumes the
explicit "for every k" presentation of polynomial-time lower bounds. -/
structure PNP_Habitant where
  L : BitLanguage
  mem_NP : InNP L
  lower_bound :
    forall M : PolyDTMCandidate,
      exists x : BitString, ¬ M.CorrectAt L x

/-- The inhabitant is exactly a separation certificate, with the target
language made explicit as data. -/
def PNP_Habitant.toSeparationCertificate
    (H : PNP_Habitant) :
    SeparationCertificate where
  target := H.L
  target_in_np := H.mem_NP
  fail_proof := H.lower_bound

def PNP_Habitant.ofSeparationCertificate
    (C : SeparationCertificate) :
    PNP_Habitant where
  L := C.target
  mem_NP := C.target_in_np
  lower_bound := C.fail_proof

/-- Once the inhabitant exists, P != NP closes with no additional material
producer. -/
theorem p_ne_np_of_habitant
    (H : PNP_Habitant) :
    PneqNP :=
  separation_certificate_closes H.toSeparationCertificate

/-- Single normative material gap. -/
def PNP_HabitantGap : Prop :=
  Nonempty PNP_Habitant

theorem pnp_habitant_gap_closes
    (h : PNP_HabitantGap) :
    PneqNP := by
  rcases h with ⟨H⟩
  exact p_ne_np_of_habitant H

/-- No extra mathematical content is hidden in SeparationCertificate:
the two payload types are mutually convertible. -/
theorem pnp_habitant_gap_iff_separation_certificate :
    PNP_HabitantGap ↔ Nonempty SeparationCertificate := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.toSeparationCertificate⟩
  · rintro ⟨C⟩
    exact ⟨PNP_Habitant.ofSeparationCertificate C⟩

/-- Canonical material inhabitant: freeze the witness language to the existing
SAT bit-language.  This is the single normative target used by ATK. -/
structure CanonicalSATPNPHabitant where
  mem_NP : InNP (CanonicalSATBoundary.SATBits CanonicalCircuitBits.circuitBitEncoding)
  lower_bound :
    UniversalFailure
      (CanonicalSATBoundary.SATBits CanonicalCircuitBits.circuitBitEncoding)

def CanonicalSATPNPHabitant.toPNP_Habitant
    (H : CanonicalSATPNPHabitant) :
    PNP_Habitant where
  L := CanonicalSATBoundary.SATBits CanonicalCircuitBits.circuitBitEncoding
  mem_NP := H.mem_NP
  lower_bound := H.lower_bound

def CanonicalSATPNPHabitantGap : Prop :=
  Nonempty CanonicalSATPNPHabitant

theorem canonical_sat_habitant_gap_iff :
    CanonicalSATPNPHabitantGap ↔
      InNP (CanonicalSATBoundary.SATBits CanonicalCircuitBits.circuitBitEncoding) ∧
      UniversalFailure
        (CanonicalSATBoundary.SATBits CanonicalCircuitBits.circuitBitEncoding) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.mem_NP, H.lower_bound⟩
  · rintro ⟨hNP, hFail⟩
    exact ⟨{ mem_NP := hNP, lower_bound := hFail }⟩

theorem canonical_sat_habitant_closes
    (H : CanonicalSATPNPHabitant) :
    PneqNP :=
  p_ne_np_of_habitant H.toPNP_Habitant

/-- The lower-bound field is the repository's canonical universal polynomial
decision failure. -/
theorem lower_bound_is_universal_failure
    (H : PNP_Habitant) :
    UniversalFailure H.L :=
  H.lower_bound

#print axioms MCore.Real.PNPHabitant.p_ne_np_of_habitant
#print axioms MCore.Real.PNPHabitant.pnp_habitant_gap_closes
#print axioms MCore.Real.PNPHabitant.pnp_habitant_gap_iff_separation_certificate
#print axioms MCore.Real.PNPHabitant.canonical_sat_habitant_gap_iff
#print axioms MCore.Real.PNPHabitant.canonical_sat_habitant_closes
#print axioms MCore.Real.PNPHabitant.lower_bound_is_universal_failure

end PNPHabitant
end Real
end MCore
