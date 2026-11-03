import MCore.Real.PNPDiscovery.PrefixPressure
import MCore.Real.P01FinalCertificate
import MCore.BackwardAudit.OrientedWitnessBoundary

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P01FinalCertificate

/--
Material theorem boundary for the canonical repository model.
These are the only two mathematical inhabitants required by the current
internal separation endpoint.  Barrier audits are intentionally not inserted
as extra assumptions here.
-/
structure MaterialSeparationPayload where
  sat_in_np : InNP (SATBits circuitBitEncoding)
  sat_universal_failure : UniversalFailure (SATBits circuitBitEncoding)

theorem material_payload_closes
    (P : MaterialSeparationPayload) :
    PneqNP :=
  target_failure_implies_p_ne_np
    P.sat_in_np
    P.sat_universal_failure

/-- Existing physical SAT-in-NP construction target. -/
def SATInNPPhysicalGap : Prop :=
  Nonempty P01MachineConstruction

theorem physical_gap_to_sat_in_np
    (H : SATInNPPhysicalGap) :
    InNP (SATBits circuitBitEncoding) := by
  rcases H with ⟨C⟩
  exact construction_closes_p01 C

/--
Exact material separation-side target used by the discovery lane.
This is deliberately the same canonical SAT language as the P01 side.
-/
def SATSeparationGap : Prop :=
  UniversalFailure (SATBits circuitBitEncoding)

/--
A complete material inhabitant contains no barrier theorem as an assumption.
The barriers constrain admissible proof strategies; they are not extra
premises of P != NP.
-/
def buildMaterialPayload
    (hNP : SATInNPPhysicalGap)
    (hSep : SATSeparationGap) :
    MaterialSeparationPayload :=
  { sat_in_np := physical_gap_to_sat_in_np hNP
    sat_universal_failure := hSep }

/-!
Technique-audit layer.

The repository presently lacks the concrete mathematical universes required
to formalize the three standard barrier results themselves.  Rather than
postulating Baker--Gill--Solovay, Razborov--Rudich, or
Aaronson--Wigderson as axioms, expose the missing formal models as typed gaps.
-/

/-- Missing prerequisite for a genuine relativization theorem: an oracle
single-tape machine model and its polynomial-time language classes. -/
structure OracleComplexityModel where
  Oracle : Type
  Language : Type
  inPWithOracle : Oracle → Language → Prop
  inNPWithOracle : Oracle → Language → Prop

/-- Baker--Gill--Solovay-shaped statement, parameterized by an explicit oracle
complexity model.  No inhabitant is supplied by this file. -/
structure RelativizationBarrierWitness
    (C : OracleComplexityModel) where
  equalityOracle : C.Oracle
  separationOracle : C.Oracle
  equality :
    ∀ L : C.Language,
      C.inPWithOracle equalityOracle L ↔
        C.inNPWithOracle equalityOracle L
  separation :
    ¬ ∀ L : C.Language,
      C.inPWithOracle separationOracle L ↔
        C.inNPWithOracle separationOracle L

def RelativizationFormalizationGap : Prop :=
  ∃ C : OracleComplexityModel,
    Nonempty (RelativizationBarrierWitness C)

/-- Minimal circuit-family universe needed before a Natural Proofs statement
can even be expressed non-vacuously. -/
structure CircuitFamilyModel where
  Family : Type
  Property : Type
  constructive : Property → Prop
  large : Property → Prop
  usefulAgainstPPoly : Property → Prop
  breaksPRG : Property → Prop
  cryptographicHardness : Prop

/-- Razborov--Rudich-shaped conditional interface.  The theorem itself is not
asserted here; an inhabitant must supply the implication in a concrete circuit
family/PRG formalization. -/
structure NaturalProofBarrierWitness
    (C : CircuitFamilyModel) where
  barrier :
    C.cryptographicHardness →
      ∀ P : C.Property,
        C.constructive P →
        C.large P →
        C.usefulAgainstPPoly P →
        C.breaksPRG P

def NaturalProofFormalizationGap : Prop :=
  ∃ C : CircuitFamilyModel,
    Nonempty (NaturalProofBarrierWitness C)

/-- Minimal data needed to state an algebrization audit.  This intentionally
does not pretend that an abstract Boolean flag is the Aaronson--Wigderson
theorem. -/
structure AlgebraicOracleModel where
  Oracle : Type
  AlgebraicExtension : Type
  extends : AlgebraicExtension → Oracle → Prop
  routeSurvives : AlgebraicExtension → Prop
  separates : Oracle → Prop

structure AlgebrizationBarrierWitness
    (C : AlgebraicOracleModel) where
  positiveWorld : C.Oracle
  negativeWorld : C.Oracle
  positiveExtension : C.AlgebraicExtension
  negativeExtension : C.AlgebraicExtension
  positive_extends : C.extends positiveExtension positiveWorld
  negative_extends : C.extends negativeExtension negativeWorld
  positive_survives : C.routeSurvives positiveExtension
  negative_survives : C.routeSurvives negativeExtension
  worlds_disagree :
    C.separates positiveWorld ↔ ¬ C.separates negativeWorld

def AlgebrizationFormalizationGap : Prop :=
  ∃ C : AlgebraicOracleModel,
    Nonempty (AlgebrizationBarrierWitness C)

/-- Machine-readable discovery ledger.  The first two fields are MATERIAL.
The last three are METHOD_AUDIT and may never be used as substitutes for the
material fields. -/
structure PNPAllGaps where
  satInNP : Prop
  separation : Prop
  relativizationAudit : Prop
  naturalProofAudit : Prop
  algebrizationAudit : Prop

def currentAllGaps : PNPAllGaps :=
  { satInNP := SATInNPPhysicalGap
    separation := SATSeparationGap
    relativizationAudit := RelativizationFormalizationGap
    naturalProofAudit := NaturalProofFormalizationGap
    algebrizationAudit := AlgebrizationFormalizationGap }

/-- Even a complete barrier audit does not manufacture the material
separation theorem.  The endpoint still explicitly requires the two material
inhabitants. -/
theorem audited_material_closure
    (_hRel : RelativizationFormalizationGap)
    (_hNat : NaturalProofFormalizationGap)
    (_hAlg : AlgebrizationFormalizationGap)
    (hNP : SATInNPPhysicalGap)
    (hSep : SATSeparationGap) :
    PneqNP :=
  material_payload_closes (buildMaterialPayload hNP hSep)

#print axioms MCore.Real.PNPDiscovery.material_payload_closes
#print axioms MCore.Real.PNPDiscovery.physical_gap_to_sat_in_np
#print axioms MCore.Real.PNPDiscovery.audited_material_closure

end PNPDiscovery
end Real
end MCore
