import MCore.Real.FinalExternal

namespace MCore.Real

open CircuitK1

noncomputable section
open Classical

inductive CollapseState
  | start
  | accept
  | reject
  deriving DecidableEq, Repr

inductive CollapseSymbol
  | blank
  | payload (phi : Circuit)
  deriving Repr

/-- Countermodel to the intended machine-complexity semantics:
the unrestricted symbol type may carry the whole Circuit in one cell, and
the Lean transition function may branch on an arbitrary proposition. -/
noncomputable def collapseSATMachine : TM CollapseState CollapseSymbol :=
  {
    initial := .start
    blank := .blank
    transition := fun q s =>
      match q, s with
      | .start, .payload phi =>
          if SATLanguage phi then
            (.accept, s, .stay)
          else
            (.reject, s, .stay)
      | .start, .blank => (.reject, .blank, .stay)
      | .accept, s => (.accept, s, .stay)
      | .reject, s => (.reject, s, .stay)
    halting := fun q =>
      match q with
      | .start => false
      | .accept => true
      | .reject => true
  }

def collapseAccepting : CollapseState → Bool
  | .accept => true
  | _ => false

def collapseEncode (phi : Circuit) :
    Configuration CollapseState CollapseSymbol :=
  {
    state := .start
    tape := {
      left := []
      head := .payload phi
      right := []
    }
  }

def collapseTimeBound : TimeBound := fun _ => 1

theorem collapseTimeBound_poly :
    PolynomialTimeBound collapseTimeBound := by
  refine ⟨1, 0, ?_⟩
  intro n
  simp [collapseTimeBound]

noncomputable def collapseSATCandidate : PolyDTMCandidate :=
  {
    State := CollapseState
    Symbol := CollapseSymbol
    machine := collapseSATMachine
    accepting := collapseAccepting
    encode := collapseEncode
    timeBound := collapseTimeBound
    encode_initial := by
      intro phi
      rfl
    time_poly := collapseTimeBound_poly
  }

theorem collapseSATCandidate_correctAt
    (phi : Circuit) :
    collapseSATCandidate.CorrectAt SATLanguage phi := by
  classical
  unfold PolyDTMCandidate.CorrectAt
  constructor
  · unfold TM.HaltsWithin
    by_cases h : SATLanguage phi
    · simp [collapseSATCandidate, collapseSATMachine, collapseEncode,
        collapseTimeBound, TM.run, TM.step, h]
    · simp [collapseSATCandidate, collapseSATMachine, collapseEncode,
        collapseTimeBound, TM.run, TM.step, h]
  · by_cases h : SATLanguage phi
    · simp [collapseSATCandidate, collapseSATMachine, collapseAccepting,
        collapseEncode, collapseTimeBound, TM.run, TM.step, h]
    · simp [collapseSATCandidate, collapseSATMachine, collapseAccepting,
        collapseEncode, collapseTimeBound, TM.run, TM.step, h]

noncomputable def collapseSATRealization :
    PolyDTMRealization SATLanguage :=
  {
    candidate := collapseSATCandidate
    decides := collapseSATCandidate_correctAt
  }

theorem sat_in_p_in_current_unrestricted_model :
    InP SATLanguage :=
  ⟨collapseSATRealization⟩

/-- Therefore the present lower-bound certificate cannot be inhabited in this
unrestricted model.  This is a model falsification, not a statement about
standard Turing-machine P versus NP. -/
theorem no_sat_lower_bound_certificate_in_current_model :
    ¬ SATLowerBoundCertificate := by
  intro cert
  exact (sat_not_in_p_of_lower_bound_certificate cert)
    sat_in_p_in_current_unrestricted_model

theorem no_final_external_certificate_in_current_model :
    ¬ FinalExternalCertificate := by
  rintro ⟨E⟩
  exact no_sat_lower_bound_certificate_in_current_model E.satLowerBound

#print axioms MCore.Real.collapseSATCandidate_correctAt
#print axioms MCore.Real.sat_in_p_in_current_unrestricted_model
#print axioms MCore.Real.no_sat_lower_bound_certificate_in_current_model
#print axioms MCore.Real.no_final_external_certificate_in_current_model

end
end MCore.Real
