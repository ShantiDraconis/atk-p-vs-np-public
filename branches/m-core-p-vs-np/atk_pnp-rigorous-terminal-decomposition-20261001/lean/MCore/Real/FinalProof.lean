import MCore.Real.SATMachine

namespace MCore
namespace Real

open CircuitK1

/-- Languages over the repository's concrete Circuit input type. -/
abbrev CircuitLanguage := Circuit → Prop

/-- Explicit polynomial bound for the concrete machine model.
    The coefficient and exponent are fixed for the machine, not for the input. -/
def PolynomialTimeBound (T : TimeBound) : Prop :=
  ∃ coefficient exponent : Nat, ∀ n : Nat,
    T n ≤ coefficient * (n + 1) ^ exponent

/-- A deterministic polynomial-time candidate, before claiming that it decides
    any particular language.  This is the domain quantified over by the direct
    fail-proof target. -/
structure PolyDTMCandidate where
  State : Type
  Symbol : Type
  machine : TM State Symbol
  accepting : State → Bool
  encode : Circuit → Configuration State Symbol
  timeBound : TimeBound
  encode_initial :
    ∀ φ : Circuit, (encode φ).state = machine.initial
  time_poly :
    PolynomialTimeBound timeBound

/-- Exact correctness condition for one input. -/
def PolyDTMCandidate.CorrectAt
    (candidate : PolyDTMCandidate)
    (language : CircuitLanguage)
    (φ : Circuit) : Prop :=
  candidate.machine.HaltsWithin
      (candidate.timeBound (CircuitK1.size φ))
      (candidate.encode φ) ∧
    (candidate.accepting
        (candidate.machine.run
          (candidate.timeBound (CircuitK1.size φ))
          (candidate.encode φ)).state = true
      ↔ language φ)

/-- A deterministic polynomial-time realization is exactly a candidate that is
    correct on every input. -/
structure PolyDTMRealization (language : CircuitLanguage) where
  candidate : PolyDTMCandidate
  decides :
    ∀ φ : Circuit, candidate.CorrectAt language φ

/-- Nondeterministic polynomial-time realization of one Circuit language.
    This reuses the already-certified NTM.DecidesWithin contract. -/
structure PolyNTMRealization (language : CircuitLanguage) where
  State : Type
  Symbol : Type
  machine : NTM State Symbol
  encode : Circuit → Configuration State Symbol
  timeBound : TimeBound
  encode_initial :
    ∀ φ : Circuit, (encode φ).state = machine.initial
  time_poly :
    PolynomialTimeBound timeBound
  decides :
    NTM.DecidesWithin
      machine encode CircuitK1.size language timeBound

/-- Concrete machine-model P and NP predicates used by the direct final-proof
    attack. These are internal definitions; equivalence with any external
    presentation of P/NP is a separate model-equivalence theorem. -/
def InP (language : CircuitLanguage) : Prop :=
  Nonempty (PolyDTMRealization language)

def InNP (language : CircuitLanguage) : Prop :=
  Nonempty (PolyNTMRealization language)

/-- Separation endpoint for the concrete machine model. -/
def MachinePneqNP : Prop :=
  ¬ ∀ language : CircuitLanguage, InP language ↔ InNP language

/-- SAT is in NP for this model. Constructing this witness is infrastructure,
    not the separation lower bound itself. -/
def SATInNP : Prop :=
  InNP SATLanguage

/-- Direct lower-bound target: no deterministic polynomial-time realization
    decides SAT in this concrete model. -/
def SATNotInP : Prop :=
  ¬ InP SATLanguage

/-- One explicit failure of one polynomial-time deterministic candidate. -/
def PolyDTMCandidate.FailsOn
    (candidate : PolyDTMCandidate)
    (language : CircuitLanguage)
    (φ : Circuit) : Prop :=
  ¬ candidate.CorrectAt language φ

/-- Operational universal lower bound: every deterministic polynomial-time SAT
    candidate has a concrete input on which it fails. -/
def UniversalSATFailure : Prop :=
  ∀ candidate : PolyDTMCandidate,
    ∃ φ : Circuit, candidate.FailsOn SATLanguage φ

/-- The fail-proof statement excludes every genuine SAT realization. -/
theorem universal_sat_failure_implies_sat_not_in_p
    (hFail : UniversalSATFailure) :
    SATNotInP := by
  intro hP
  rcases hP with ⟨realization⟩
  rcases hFail realization.candidate with ⟨φ, hBad⟩
  exact hBad (realization.decides φ)

/-- Conversely, non-membership in P forces a failing input for every candidate.
    This direction uses only classical propositional reasoning. -/
theorem sat_not_in_p_implies_universal_sat_failure
    (hNotP : SATNotInP) :
    UniversalSATFailure := by
  intro candidate
  apply Classical.byContradiction
  intro hNoFailure
  apply hNotP
  refine ⟨{ candidate := candidate, decides := ?_ }⟩
  intro φ
  apply Classical.byContradiction
  intro hBad
  exact hNoFailure ⟨φ, hBad⟩

theorem universal_sat_failure_iff_sat_not_in_p :
    UniversalSATFailure ↔ SATNotInP := by
  constructor
  · exact universal_sat_failure_implies_sat_not_in_p
  · exact sat_not_in_p_implies_universal_sat_failure

/-- Positive certificate form of the lower-bound target.
    Unlike timing evidence, its payload is universal over every polynomial-time
    deterministic candidate and produces a failing SAT instance for each one. -/
structure SATLowerBoundCertificate : Prop where
  fail_proof : UniversalSATFailure

theorem sat_not_in_p_of_lower_bound_certificate
    (cert : SATLowerBoundCertificate) :
    SATNotInP :=
  universal_sat_failure_implies_sat_not_in_p cert.fail_proof

theorem lower_bound_certificate_of_sat_not_in_p
    (hNotP : SATNotInP) :
    SATLowerBoundCertificate :=
  ⟨sat_not_in_p_implies_universal_sat_failure hNotP⟩

theorem sat_lower_bound_certificate_iff :
    SATLowerBoundCertificate ↔ SATNotInP := by
  constructor
  · exact sat_not_in_p_of_lower_bound_certificate
  · exact lower_bound_certificate_of_sat_not_in_p

/-- Direct endpoint compression. No NP-completeness theorem is required:
    one language in NP but outside P already separates the two classes. -/
theorem sat_boundary_implies_machine_p_ne_np
    (hNP : SATInNP)
    (hNotP : SATNotInP) :
    MachinePneqNP := by
  intro hEq
  exact hNotP ((hEq SATLanguage).mpr hNP)

/-- Certificate-shaped final theorem. -/
theorem sat_certificate_implies_machine_p_ne_np
    (hNP : SATInNP)
    (cert : SATLowerBoundCertificate) :
    MachinePneqNP :=
  sat_boundary_implies_machine_p_ne_np
    hNP (sat_not_in_p_of_lower_bound_certificate cert)

/-- The direct FINAL_PROOF residual.
    The first conjunct is the concrete NP witness.
    The second conjunct is the genuine universal deterministic fail proof.
    No benchmark, finite search, C12/C13 table, or elliptic-curve timing result
    inhabits this proposition by definition. -/
def FINAL_PROOF_RESIDUAL : Prop :=
  SATInNP ∧ SATLowerBoundCertificate

theorem final_proof_from_residual
    (h : FINAL_PROOF_RESIDUAL) :
    MachinePneqNP := by
  exact sat_certificate_implies_machine_p_ne_np h.1 h.2

#print axioms MCore.Real.universal_sat_failure_implies_sat_not_in_p
#print axioms MCore.Real.sat_not_in_p_implies_universal_sat_failure
#print axioms MCore.Real.universal_sat_failure_iff_sat_not_in_p
#print axioms MCore.Real.sat_boundary_implies_machine_p_ne_np
#print axioms MCore.Real.sat_certificate_implies_machine_p_ne_np
#print axioms MCore.Real.final_proof_from_residual

end Real
end MCore
