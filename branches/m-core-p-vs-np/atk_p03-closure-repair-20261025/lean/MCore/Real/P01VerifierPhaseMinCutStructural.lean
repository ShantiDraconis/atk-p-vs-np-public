import MCore.Real.P01WitnessPrepGlobal

namespace MCore
namespace Real
namespace P01VerifierPhaseMinCutStructural

open CanonicalFinalProof
open CanonicalCircuitBits
open P01IntegratedAssembly
open P01WitnessPrepGlobal

/--
Exact mechanical min-cut for P01.

The prep phase is already constructed. Therefore a single inhabitant of
`P01VerifierPhase prepPhase.layout` is sufficient to construct the official
P01 machine object; no additional parser/witness/verifier wiring theorem is
needed after this point.
-/
abbrev P01MechanicalMinCut : Prop :=
  Nonempty (P01VerifierPhase prepPhase.layout)

theorem p01ConstructionGap_of_verifierPhase
    (h : P01MechanicalMinCut) :
    P01FinalCertificate.P01ConstructionGap := by
  rcases h with ⟨V⟩
  exact p01_of_verifier V

#print axioms MCore.Real.P01VerifierPhaseMinCutStructural.p01ConstructionGap_of_verifierPhase

end P01VerifierPhaseMinCutStructural
end Real
end MCore
