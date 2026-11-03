import MCore.Real.P02SemanticSelfSubstitution
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02FiniteClockNormalization

open CanonicalFinalProof
open P02SemanticSelfSubstitution
open MachineRunLemmas

noncomputable def clockCoeff (M : PolyDTMCandidate) : Nat :=
  Classical.choose M.time_poly

noncomputable def clockExp (M : PolyDTMCandidate) : Nat :=
  Classical.choose (Classical.choose_spec M.time_poly)

theorem timeBound_le_explicitEnvelope
    (M : PolyDTMCandidate) :
    ∀ n : Nat,
      M.timeBound n ≤ clockCoeff M * (n + 1) ^ clockExp M := by
  intro n
  exact (Classical.choose_spec
    (Classical.choose_spec
      M.time_poly)) n

noncomputable def explicitEnvelope
    (M : PolyDTMCandidate) : TimeBound :=
  fun n => clockCoeff M * (n + 1) ^ clockExp M

theorem explicitEnvelope_poly
    (M : PolyDTMCandidate) :
    PolynomialTimeBound (explicitEnvelope M) := by
  refine ⟨clockCoeff M, clockExp M, ?_⟩
  intro n
  rfl

noncomputable def normalizedCandidate
    (M : PolyDTMCandidate) : PolyDTMCandidate :=
  { stateCount := M.stateCount
    machine := M.machine
    blank_none := M.blank_none
    accepting := M.accepting
    timeBound := explicitEnvelope M
    time_poly := explicitEnvelope_poly M }

theorem normalizedCandidate_machine
    (M : PolyDTMCandidate) :
    (normalizedCandidate M).machine = M.machine := rfl

theorem normalizedCandidate_accepting
    (M : PolyDTMCandidate) :
    (normalizedCandidate M).accepting = M.accepting := rfl

theorem normalizedCandidate_total
    (M : PolyDTMCandidate)
    (hTotal : ∀ x : BitString, OwnClockHalts M x) :
    ∀ x : BitString, OwnClockHalts (normalizedCandidate M) x := by
  intro x
  unfold OwnClockHalts normalizedCandidate explicitEnvelope
  exact haltsWithin_mono
    M.machine
    (initialTMConfig M.machine x)
    (timeBound_le_explicitEnvelope M x.length)
    (hTotal x)

theorem normalized_run_eq
    (M : PolyDTMCandidate)
    (x : BitString)
    (hx : OwnClockHalts M x) :
    M.machine.run
        ((normalizedCandidate M).timeBound x.length)
        (initialTMConfig M.machine x) =
      M.machine.run
        (M.timeBound x.length)
        (initialTMConfig M.machine x) := by
  let halted :=
    M.machine.run
      (M.timeBound x.length)
      (initialTMConfig M.machine x)
  have hrun :
      M.machine.run
          (M.timeBound x.length)
          (initialTMConfig M.machine x) = halted := rfl
  have hhalt :
      M.machine.halting halted.state = true := by
    exact hx
  have hle :
      M.timeBound x.length ≤
        (normalizedCandidate M).timeBound x.length := by
    exact timeBound_le_explicitEnvelope M x.length
  exact
    run_to_larger_fuel_of_halt
      M.machine
      (initialTMConfig M.machine x)
      halted
      hle hrun hhalt

theorem normalized_observedBit_eq
    (M : PolyDTMCandidate)
    (x : BitString)
    (hx : OwnClockHalts M x) :
    observedBit (normalizedCandidate M) x =
      observedBit M x := by
  have hrun := normalized_run_eq M x hx
  have hacc :=
    congrArg (fun c => M.accepting c.state) hrun
  simpa [observedBit, normalizedCandidate] using hacc

theorem normalized_semantics_on_total
    (M : PolyDTMCandidate)
    (hTotal : ∀ x : BitString, OwnClockHalts M x) :
    ∀ x : BitString,
      observedBit (normalizedCandidate M) x =
        observedBit M x := by
  intro x
  exact normalized_observedBit_eq M x (hTotal x)

#print axioms MCore.Real.P02FiniteClockNormalization.timeBound_le_explicitEnvelope
#print axioms MCore.Real.P02FiniteClockNormalization.normalizedCandidate_total
#print axioms MCore.Real.P02FiniteClockNormalization.normalized_run_eq
#print axioms MCore.Real.P02FiniteClockNormalization.normalized_observedBit_eq

end P02FiniteClockNormalization
end Real
end MCore
