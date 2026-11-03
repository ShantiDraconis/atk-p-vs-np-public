import MCore.Real.P01WitnessPrepGlobal
import MCore.Real.P01RawVerifierMaterialCore
import MCore.Real.P01CheckedVerifierFiniteState
import MCore.Real.P01IntegratedAssembly
import MCore.Real.P01MaterialGlobalBudget

namespace MCore
namespace Real
namespace P01MaterialInhabitantFrontier

open CanonicalFinalProof
open P01WitnessPreservingPrep
open P01WitnessPrepGlobal
open P01IntegratedAssembly
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierFiniteState
open P01MaterialGlobalBudget
open P01RawVerifierMaterialCore
open P01GuessedWitnessRelation

theorem prep_phase_inhabited :
    Nonempty P01PrepPhase :=
  ⟨prepPhase⟩

/-- Raw checked-verifier semantics packaged directly into the explicit-state
verifier interface.  Relabelling to Fin is performed once, downstream, by
P01IntegratedAssembly.verifierFinMachine. -/
def verifierPhaseOfRawCore
    (K : RawVerifierMaterialCore) :
    P01VerifierPhase prepPhase.layout where
  State := CheckedVerifierState
  stateCount := checkedVerifierStateCount
  encode := checkedVerifierStateEncode
  decode := checkedVerifierStateDecode
  decode_encode := checkedVerifierStateDecode_encode
  machine := checkedVerifierMachine
  blank_none := checkedVerifierMachine_blank
  timeBound := terminalVerifierTimeBound
  time_poly := terminalVerifierTimeBound_poly
  halts := by
    intro bs w hw
    simpa [prepPhase_layout] using K.halts bs w hw
  correct := by
    intro bs w hw
    simpa [prepPhase_layout] using K.correct bs w hw

theorem p01_of_raw_material_core
    (K : RawVerifierMaterialCore) :
    P01FinalCertificate.P01ConstructionGap :=
  p01_of_phases prepPhase (verifierPhaseOfRawCore K)

theorem p01_reduced_to_raw_core :
    RawVerifierMaterialCore →
      P01FinalCertificate.P01ConstructionGap :=
  p01_of_raw_material_core

#print axioms MCore.Real.P01MaterialInhabitantFrontier.prep_phase_inhabited
#print axioms MCore.Real.P01MaterialInhabitantFrontier.verifierPhaseOfRawCore
#print axioms MCore.Real.P01MaterialInhabitantFrontier.p01_of_raw_material_core
#print axioms MCore.Real.P01MaterialInhabitantFrontier.p01_reduced_to_raw_core

end P01MaterialInhabitantFrontier
end Real
end MCore
