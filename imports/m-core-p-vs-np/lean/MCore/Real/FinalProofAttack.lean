import MCore.Real.FinalProof

namespace MCore
namespace Real
namespace FinalProofAttack

/-- Two-state halting shell encoded as Option Bool:
    none = running, some b = halted with answer bit b. -/
def smuggledMachine : TM (Option Bool) Bool :=
  { initial := none
    blank := false
    transition := fun state symbol =>
      match state with
      | none => (some symbol, symbol, .stay)
      | some b => (some b, symbol, .stay)
    halting := fun state =>
      match state with
      | none => false
      | some _ => true }

/-- Read acceptance directly from the halted answer state. -/
def smuggledAccepting : Option Bool → Bool
  | some true => true
  | _ => false

/-- This is precisely the loophole under attack:
    the arbitrary encoder computes membership before machine time starts and
    writes the answer bit into the initial tape. -/
noncomputable def smuggledEncode
    (language : CircuitLanguage)
    (φ : CircuitK1.Circuit) :
    Configuration (Option Bool) Bool :=
  letI : Decidable (language φ) := Classical.propDecidable (language φ)
  { state := none
    tape :=
      { left := []
        head := if language φ then true else false
        right := [] } }

noncomputable def smuggledCandidate
    (language : CircuitLanguage) :
    PolyDTMCandidate :=
  { State := Option Bool
    Symbol := Bool
    machine := smuggledMachine
    accepting := smuggledAccepting
    encode := smuggledEncode language
    timeBound := fun _ => 1
    encode_initial := by
      intro φ
      rfl
    time_poly := by
      refine ⟨1, 0, ?_⟩
      intro n
      simp [PolynomialTimeBound] }

theorem smuggledCandidate_correct
    (language : CircuitLanguage) :
    ∀ φ : CircuitK1.Circuit,
      (smuggledCandidate language).CorrectAt language φ := by
  intro φ
  classical
  by_cases h : language φ
  · simp [PolyDTMCandidate.CorrectAt,
      smuggledCandidate, smuggledMachine, smuggledAccepting,
      smuggledEncode, TM.HaltsWithin, TM.run, TM.step,
      Tape.write, Tape.move, h]
  · simp [PolyDTMCandidate.CorrectAt,
      smuggledCandidate, smuggledMachine, smuggledAccepting,
      smuggledEncode, TM.HaltsWithin, TM.run, TM.step,
      Tape.write, Tape.move, h]

noncomputable def smuggledRealization
    (language : CircuitLanguage) :
    PolyDTMRealization language :=
  { candidate := smuggledCandidate language
    decides := smuggledCandidate_correct language }

/-- FAIL TEST: under the current arbitrary-encode definition, every language
    has a one-step deterministic polynomial-time realization. -/
theorem every_language_inP_under_arbitrary_encode
    (language : CircuitLanguage) :
    InP language := by
  exact ⟨smuggledRealization language⟩

/-- Therefore SATNotInP is false in the current model independently of the
    actual P-vs-NP question. -/
theorem current_SATNotInP_refuted :
    ¬ SATNotInP := by
  intro h
  exact h (every_language_inP_under_arbitrary_encode SATLanguage)

/-- Consequently the current UniversalSATFailure target is also false. -/
theorem current_UniversalSATFailure_refuted :
    ¬ UniversalSATFailure := by
  intro h
  exact current_SATNotInP_refuted
    (universal_sat_failure_implies_sat_not_in_p h)

/-- And the certificate type is uninhabited in this flawed model. -/
theorem current_SATLowerBoundCertificate_refuted :
    ¬ SATLowerBoundCertificate := by
  intro cert
  exact current_SATNotInP_refuted
    (sat_not_in_p_of_lower_bound_certificate cert)

#print axioms MCore.Real.FinalProofAttack.smuggledCandidate_correct
#print axioms MCore.Real.FinalProofAttack.every_language_inP_under_arbitrary_encode
#print axioms MCore.Real.FinalProofAttack.current_SATNotInP_refuted
#print axioms MCore.Real.FinalProofAttack.current_UniversalSATFailure_refuted
#print axioms MCore.Real.FinalProofAttack.current_SATLowerBoundCertificate_refuted

end FinalProofAttack
end Real
end MCore
