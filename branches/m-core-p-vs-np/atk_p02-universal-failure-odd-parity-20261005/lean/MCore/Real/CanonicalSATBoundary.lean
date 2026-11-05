import MCore.Real.CNFStructure
import MCore.Real.Semantics
import MCore.Real.SATMachine
import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace CanonicalSATBoundary

open CircuitK1
open CanonicalFinalProof
open FailProofAllGaps

/-- A semantics-preserving bitstring boundary for the existing Circuit AST.
    Circuit remains the syntax; this does not introduce a second SAT syntax. -/
structure CircuitBitEncoding where
  encode : Circuit → BitString
  decode : BitString → Option Circuit
  decode_encode : ∀ φ : Circuit, decode (encode φ) = some φ

/-- SAT language induced on bitstrings by one exact Circuit encoding. -/
def SATBits (E : CircuitBitEncoding) : BitLanguage :=
  fun x =>
    ∃ φ : Circuit,
      E.decode x = some φ ∧ SATLanguage φ

theorem encoded_sat_iff
    (E : CircuitBitEncoding)
    (φ : Circuit) :
    SATBits E (E.encode φ) ↔ SATLanguage φ := by
  constructor
  · rintro ⟨ψ, hdecode, hsat⟩
    rw [E.decode_encode φ] at hdecode
    have hEq : φ = ψ := Option.some.inj hdecode
    simpa [hEq] using hsat
  · intro hsat
    exact ⟨φ, E.decode_encode φ, hsat⟩

/-- G1a: an actual exact bit encoding of the existing Circuit syntax. -/
def SATEncodingGap : Prop :=
  Nonempty CircuitBitEncoding

/-- G1b: after fixing an encoding, the induced SAT bit-language has a concrete
    polynomial-time nondeterministic machine in the hardened model. -/
def SATInNPGap (E : CircuitBitEncoding) : Prop :=
  InNP (SATBits E)

/-- G2: the genuine lower-bound/fail-proof object for the same SAT language. -/
def SATFailGap (E : CircuitBitEncoding) : Prop :=
  Nonempty (FailureGenerator (SATBits E))

/-- Full internal SAT closure. -/
structure SATInternalClosure where
  encoding : CircuitBitEncoding
  sat_in_np : SATInNPGap encoding
  fail_generator : FailureGenerator (SATBits encoding)

theorem sat_internal_closure_implies_p_ne_np
    (C : SATInternalClosure) :
    PneqNP := by
  have hFail : UniversalFailure (SATBits C.encoding) :=
    failure_generator_implies_universal_failure C.fail_generator
  exact target_failure_implies_p_ne_np C.sat_in_np hFail

/-- Full external closure adds only the model-equivalence adapter. -/
structure SATExternalClosure
    (officialP officialNP : BitLanguage → Prop)
    extends SATInternalClosure where
  model_match : ExternalModelMatch officialP officialNP

theorem sat_external_closure_implies_official_separation
    {officialP officialNP : BitLanguage → Prop}
    (C : SATExternalClosure officialP officialNP) :
    OfficialPneqNP officialP officialNP := by
  have hInternal : PneqNP :=
    sat_internal_closure_implies_p_ne_np C.toSATInternalClosure
  exact internal_separation_transfers C.model_match hInternal

#print axioms MCore.Real.CanonicalSATBoundary.encoded_sat_iff
#print axioms MCore.Real.CanonicalSATBoundary.sat_internal_closure_implies_p_ne_np
#print axioms MCore.Real.CanonicalSATBoundary.sat_external_closure_implies_official_separation

end CanonicalSATBoundary
end Real
end MCore
