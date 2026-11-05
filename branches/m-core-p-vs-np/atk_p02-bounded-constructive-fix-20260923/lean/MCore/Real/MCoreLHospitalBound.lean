import MCore.Real.P02BoundedPartSemantics
import MCore.Real.P02SemanticSelfEmbeddingClose
import MCore.Real.P01FinalCertificate
import MCore.Real.CookNormalizedG3Contract
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace MCoreLHospitalBound

open CanonicalFinalProof
open CanonicalCircuitBits
open P02BoundedPartSemantics
open P02SemanticSelfEmbeddingClose
open P01FinalCertificate
open CookNormalizedG3Contract
open FinalExternalCertificate

/--
Canonical symbolic indeterminate sector of M-Core.

These constructors are M-Core values, not ordinary naturals/reals and not
Mathlib's partial-computation bottom.  The first canonical element is I₀,
written here as `phi`.
-/
inductive MIndeterminate where
  | phi
  | infDivInf
  | zeroMulInf
  | infSubInf
  | zeroPowZero
  | onePowInf
  | infPowZero
  deriving DecidableEq, Repr

/-- The first M-Core indeterminate constant: I₀ = φ = 0/0 symbolically. -/
def I₀ : MIndeterminate :=
  .phi

/-- ASCII alias for tooling and filenames. -/
def I0 : MIndeterminate :=
  I₀

/-- Canonical symbolic phi of the M-Core indeterminate sector. -/
def phi : MIndeterminate :=
  I₀

@[simp] theorem phi_eq_I0 : phi = I0 := by
  rfl

@[simp] theorem I0_eq_first_indeterminate : I0 = MIndeterminate.phi := by
  rfl

/--
Optional bridge from a symbolic M-Core indeterminate to a partial-recursive
code.  This is deliberately data, not a theorem: a concrete code realizing
the symbol must be supplied and audited separately.
-/
structure IndeterminateCodeRealization where
  symbol : MIndeterminate
  code : Nat.Partrec.Code
  diverges : DivergesAtZero code

/-- A realization of φ is a code-level representative of the first
indeterminate constant. -/
def PhiCodeRealization : Type :=
  { R : IndeterminateCodeRealization // R.symbol = phi }

/--
M-Core indeterminate constants are codes whose semantic evaluation at the
distinguished input is bottom.  This definition is descriptive only: it does
not make semantic divergence decidable and does not assert that bottom later
becomes a finite `evaln` value.
-/
def IndeterminateConstants : Type :=
  { c : Nat.Partrec.Code // DivergesAtZero c }

/--
M-Core designation of its first indeterminate constant.  The concrete code
identifier `phi_11dd4ff2` is not yet defined in this HEAD, so the designation
is carried explicitly as data instead of inventing a code.
-/
structure FirstIndeterminateConstantData where
  code : Nat.Partrec.Code
  diverges : DivergesAtZero code

def FirstIndeterminateConstantData.asIndeterminate
    (I : FirstIndeterminateConstantData) : IndeterminateConstants :=
  ⟨I.code, I.diverges⟩

/--
A conditional M-Core package may name a distinguished first indeterminate
constant.  The intended external name is I₀ / phi_11dd4ff2; this file does not
assert that a repository code with that name already exists.
-/
def firstIndeterminateConstant
    (I : FirstIndeterminateConstantData) : IndeterminateConstants :=
  I.asIndeterminate

theorem first_is_semantic_bottom
    (I : FirstIndeterminateConstantData) :
    (firstIndeterminateConstant I).val.eval 0 = (⊥ : Part Nat) := by
  exact I.diverges

/--
Single explicit M-Core hypothesis used by the conditional lane.

Repository-level meaning: the M-Core L'Hospital rule supplies the exact
bounded diagonal witnesses required by the already-existing P02 semantic
self-embedding endpoint.  Keeping the assumption at this interface avoids the
inconsistent statement `c.eval 0 = ⊥ -> ∃ fuel, c.evaln fuel 0 = some v`,
which contradicts `evaln_sound`.

This proposition is the one unresolved assumption of this conditional module.
-/
/--
Abstract bounded-limit predicate used only to record the M-Core interpretation
of the distinguished indeterminate constant.  It is deliberately separate
from Mathlib's `Part` semantics: no theorem here states that bottom becomes a
finite `evaln` value.
-/
def MCoreLHospitalLimit
    (I : FirstIndeterminateConstantData)
    (lim : Nat) : Prop :=
  True

/--
Single explicit M-Core hypothesis used by the conditional lane.

It packages both pieces of the current M-Core convention:
1. a designated first indeterminate constant I₀;
2. the exact P02 witness producer required by the repository.

The second field is the mathematically substantive assumption that keeps the
final result conditional until independently proved.
-/
structure MCoreLHospitalWitness where
  first : FirstIndeterminateConstantData
  limit_index : Nat
  limit_rule : MCoreLHospitalLimit first limit_index
  p02_witness : UniversalWitnessExists

def MCoreLHospitalBound : Prop :=
  Nonempty MCoreLHospitalWitness

/--
Temporary explicit assumption.  Any theorem depending on this axiom remains
conditional until `MCoreLHospitalBound` is proved without this axiom.
-/
axiom MCORE_LHOSPITAL_AXIOM : MCoreLHospitalBound

/-- Conditional P02 closure under the explicit M-Core hypothesis. -/
theorem P02Target_conditional
    (h : MCoreLHospitalBound) :
    P02TerminalFrontier.P02Target := by
  rcases h with ⟨H⟩
  exact universal_witness_closes_p02 H.p02_witness

/--
Conditional external-input producer.  P01 is still supplied through the
repository's actual P01 construction producer; G3 uses the existing normalized
external contract.  No field of `FinalExternalInputs` is fabricated.
-/
theorem FinalExternalGap_conditional
    (hLH : MCoreLHospitalBound)
    (hP01 : P01ConstructionGap) :
    FinalExternalGap := by
  have hG1 : SATInNPGap circuitBitEncoding :=
    construction_closes_p01 hP01
  have hP02 : P02TerminalFrontier.P02Target :=
    P02Target_conditional hLH
  rcases hP02 with ⟨G⟩
  exact ⟨{
    g1 := hG1
    g2 := G
    g3 := cookNormalizedExternalContract
  }⟩

/--
Explicit axiom-backed conditional endpoint.  The axiom remains visible in
`#print axioms`; therefore this theorem is not an unconditional proof.
-/
theorem FinalExternalGap_assumed
    (hP01 : P01ConstructionGap) :
    FinalExternalGap :=
  FinalExternalGap_conditional MCORE_LHOSPITAL_AXIOM hP01

/--
Audit theorem: semantic bottom cannot itself yield a finite `evaln` result.
This guards the conditional M-Core rule from being misread as a theorem about
Mathlib's `Part` bottom becoming defined.
-/
theorem bottom_has_no_bounded_value
    (I : IndeterminateConstants)
    (fuel v : Nat) :
    I.val.evaln fuel 0 ≠ some v := by
  intro h
  have hall :=
    divergence_implies_all_evaln_none I.property fuel
  rw [hall] at h
  contradiction

#print axioms MCore.Real.MCoreLHospitalBound.P02Target_conditional
#print axioms MCore.Real.MCoreLHospitalBound.FinalExternalGap_conditional
#print axioms MCore.Real.MCoreLHospitalBound.FinalExternalGap_assumed
#print axioms MCore.Real.MCoreLHospitalBound.bottom_has_no_bounded_value

end MCoreLHospitalBound
end Real
end MCore
