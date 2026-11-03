import MCore.Real.P02SemanticSelfSubstitution
import MCore.Real.FailProofFiniteAttack

namespace MCore
namespace Real
namespace P02RunCollapseProbe

open CanonicalFinalProof
open P02SemanticSelfSubstitution

def alwaysAcceptMachine : TM (Fin 1) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol => (q, symbol, .stay)
    halting := fun _ => true }

def alwaysAcceptCandidate : PolyDTMCandidate :=
  { stateCount := 0
    machine := alwaysAcceptMachine
    blank_none := rfl
    accepting := fun _ => true
    timeBound := fun _ => 0
    time_poly := by
      refine ⟨0, 0, ?_⟩
      intro n
      simp [CanonicalFinalProof.PolynomialTimeBound] }

theorem alwaysReject_totalClock :
    ∀ x : BitString,
      OwnClockHalts FailProofFiniteAttack.alwaysRejectCandidate x := by
  intro x
  simp [OwnClockHalts, FailProofFiniteAttack.alwaysRejectCandidate,
    FailProofFiniteAttack.alwaysRejectMachine, initialTMConfig,
    TM.HaltsWithin, TM.run]

theorem alwaysAccept_totalClock :
    ∀ x : BitString,
      OwnClockHalts alwaysAcceptCandidate x := by
  intro x
  simp [OwnClockHalts, alwaysAcceptCandidate, alwaysAcceptMachine,
    initialTMConfig, TM.HaltsWithin, TM.run]

/-- Probe C on the concrete always-reject control. -/
theorem alwaysReject_preserves_rejectCode_halting :
    ∀ x : BitString,
      OwnClockHalts FailProofFiniteAttack.alwaysRejectCandidate x →
      OwnClockHalts FailProofFiniteAttack.alwaysRejectCandidate
        (rejectCode FailProofFiniteAttack.alwaysRejectCandidate x) := by
  intro x _
  exact alwaysReject_totalClock _

/-- Probe C on the concrete always-accept control. -/
theorem alwaysAccept_preserves_rejectCode_halting :
    ∀ x : BitString,
      OwnClockHalts alwaysAcceptCandidate x →
      OwnClockHalts alwaysAcceptCandidate
        (rejectCode alwaysAcceptCandidate x) := by
  intro x _
  exact alwaysAccept_totalClock _

theorem alwaysReject_semanticClosure_empty :
    SemanticClosureAt FailProofFiniteAttack.alwaysRejectCandidate [] := by
  rfl

theorem alwaysAccept_semanticClosure_empty :
    SemanticClosureAt alwaysAcceptCandidate [] := by
  rfl

/-- Probe D/clock-collapse on the concrete always-reject control. -/
theorem alwaysReject_clockCollapse :
    ∃ x : BitString,
      FailProofFiniteAttack.alwaysRejectCandidate.timeBound
          (rejectCode FailProofFiniteAttack.alwaysRejectCandidate x).length ≤
        FailProofFiniteAttack.alwaysRejectCandidate.timeBound x.length ∧
      SemanticClosureAt FailProofFiniteAttack.alwaysRejectCandidate x := by
  refine ⟨[], ?_, alwaysReject_semanticClosure_empty⟩
  rfl

/-- Probe D/clock-collapse on the concrete always-accept control. -/
theorem alwaysAccept_clockCollapse :
    ∃ x : BitString,
      alwaysAcceptCandidate.timeBound (rejectCode alwaysAcceptCandidate x).length ≤
        alwaysAcceptCandidate.timeBound x.length ∧
      SemanticClosureAt alwaysAcceptCandidate x := by
  refine ⟨[], ?_, alwaysAccept_semanticClosure_empty⟩
  rfl

theorem alwaysReject_runCollapse :
    ∃ x : BitString,
      observedBit FailProofFiniteAttack.alwaysRejectCandidate
          (rejectCode FailProofFiniteAttack.alwaysRejectCandidate x) =
        observedBit FailProofFiniteAttack.alwaysRejectCandidate x := by
  exact ⟨[], alwaysReject_semanticClosure_empty⟩

theorem alwaysAccept_runCollapse :
    ∃ x : BitString,
      observedBit alwaysAcceptCandidate (rejectCode alwaysAcceptCandidate x) =
        observedBit alwaysAcceptCandidate x := by
  exact ⟨[], alwaysAccept_semanticClosure_empty⟩

#print axioms MCore.Real.P02RunCollapseProbe.alwaysReject_preserves_rejectCode_halting
#print axioms MCore.Real.P02RunCollapseProbe.alwaysAccept_preserves_rejectCode_halting
#print axioms MCore.Real.P02RunCollapseProbe.alwaysReject_clockCollapse
#print axioms MCore.Real.P02RunCollapseProbe.alwaysAccept_clockCollapse
#print axioms MCore.Real.P02RunCollapseProbe.alwaysReject_runCollapse
#print axioms MCore.Real.P02RunCollapseProbe.alwaysAccept_runCollapse

end P02RunCollapseProbe
end Real
end MCore
