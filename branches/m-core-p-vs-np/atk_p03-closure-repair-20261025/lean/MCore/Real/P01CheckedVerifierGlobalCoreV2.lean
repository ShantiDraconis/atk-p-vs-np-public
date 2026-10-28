import MCore.Real.P01CheckedVerifierManualFiniteState
import MCore.Real.P01WitnessPrepGlobal

namespace MCore
namespace Real
namespace P01CheckedVerifierGlobalCoreV2

open CanonicalFinalProof
open CanonicalCircuitBits
open P01IntegratedAssembly
open P01WitnessPrepGlobal
open P01WitnessPreservingPrep
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierManualFiniteState
open P01NTMRunLaws

/-- Exact remaining P01 mechanical payload after machine choice, tape layout,
state coding and final parser/witness/verifier assembly have all been fixed.

This structure contains no machine field: the machine is
checkedVerifierMachine, relabelled by the explicit manual state codec.
Therefore an inhabitant can only come from the two global execution facts and
one polynomial bound. -/
structure CheckedVerifierGlobalCore where
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts : ∀ (bs w : BitString), w.length = bs.length →
    checkedVerifierMachine.HaltsWithin
      (timeBound bs.length)
      { state := checkedVerifierMachine.initial,
        tape := preparedTape w bs }
  correct : ∀ (bs w : BitString), w.length = bs.length →
    (checkedVerifierMachine.AcceptsWithin
        (timeBound bs.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape w bs } ↔
      P01GuessedWitnessRelation.VerifyBits bs w)

/-- The exact global core packages into the already-reduced verifier phase. -/
def CheckedVerifierGlobalCore.toVerifierPhase
    (C : CheckedVerifierGlobalCore) :
    P01VerifierPhase prepPhase.layout where
  stateCount := checkedVerifierStateCount
  machine := checkedVerifierFinMachine
  blank_none := checkedVerifierFinMachine_blank
  timeBound := C.timeBound
  time_poly := C.time_poly
  halts := by
    intro bs w hw
    have h := C.halts bs w hw
    have hfin :
        checkedVerifierFinMachine.HaltsWithin (C.timeBound bs.length)
          (liftConfig checkedVerifierStateEncode
            { state := checkedVerifierMachine.initial,
              tape := preparedTape w bs }) :=
      (checkedVerifierFinMachine_haltsWithin_iff
        (C.timeBound bs.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape w bs }).2 h
    simpa [prepPhase_layout, checkedVerifierFinMachine,
      P01IntegratedAssembly.relabel, liftConfig] using hfin
  correct := by
    intro bs w hw
    have h := C.correct bs w hw
    have hfin :
        (checkedVerifierFinMachine.AcceptsWithin (C.timeBound bs.length)
            (liftConfig checkedVerifierStateEncode
              { state := checkedVerifierMachine.initial,
                tape := preparedTape w bs }) ↔
          P01GuessedWitnessRelation.VerifyBits bs w) :=
      (checkedVerifierFinMachine_acceptsWithin_iff
        (C.timeBound bs.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape w bs }).trans h
    simpa [prepPhase_layout, checkedVerifierFinMachine,
      P01IntegratedAssembly.relabel, liftConfig] using hfin

/-- No integration theorem remains after the global execution core. -/
theorem p01ConstructionGap_of_core
    (C : CheckedVerifierGlobalCore) :
    P01FinalCertificate.P01ConstructionGap :=
  p01_of_verifier C.toVerifierPhase

abbrev P01MechanicalGlobalExecutionGap : Prop :=
  Nonempty CheckedVerifierGlobalCore

theorem mechanical_gap_closes_p01
    (h : P01MechanicalGlobalExecutionGap) :
    P01FinalCertificate.P01ConstructionGap := by
  rcases h with ⟨C⟩
  exact p01ConstructionGap_of_core C

#print axioms MCore.Real.P01CheckedVerifierGlobalCoreV2.CheckedVerifierGlobalCore.toVerifierPhase
#print axioms MCore.Real.P01CheckedVerifierGlobalCoreV2.p01ConstructionGap_of_core
#print axioms MCore.Real.P01CheckedVerifierGlobalCoreV2.mechanical_gap_closes_p01

end P01CheckedVerifierGlobalCoreV2
end Real
end MCore
