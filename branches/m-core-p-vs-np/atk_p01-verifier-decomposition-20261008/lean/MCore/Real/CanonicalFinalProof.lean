import MCore.Real.Model

namespace MCore
namespace Real
namespace CanonicalFinalProof

abbrev BitString := List Bool
abbrev BitLanguage := BitString → Prop

/-- Canonical tape encoding. none is the blank/end marker, so the empty input
    is distinct from an input beginning with false. -/
def inputTape : BitString → Tape (Option Bool)
  | [] =>
      { left := []
        head := none
        right := [] }
  | b :: bs =>
      { left := []
        head := some b
        right := bs.map some }

def initialTMConfig
    {stateCount : Nat}
    (machine : TM (Fin (stateCount + 1)) (Option Bool))
    (x : BitString) :
    Configuration (Fin (stateCount + 1)) (Option Bool) :=
  { state := machine.initial
    tape := inputTape x }

def initialNTMConfig
    {stateCount : Nat}
    (machine : NTM (Fin (stateCount + 1)) (Option Bool))
    (x : BitString) :
    Configuration (Fin (stateCount + 1)) (Option Bool) :=
  { state := machine.initial
    tape := inputTape x }

/-- Polynomial bound with constants fixed per machine. -/
def PolynomialTimeBound (T : TimeBound) : Prop :=
  ∃ coefficient exponent : Nat, ∀ n : Nat,
    T n ≤ coefficient * (n + 1) ^ exponent

/-- Hardened deterministic candidate:
    finite control, fixed alphabet, canonical input, blank = none,
    and no arbitrary input encoder field. -/
structure PolyDTMCandidate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def PolyDTMCandidate.CorrectAt
    (candidate : PolyDTMCandidate)
    (language : BitLanguage)
    (x : BitString) : Prop :=
  let config := initialTMConfig candidate.machine x
  candidate.machine.HaltsWithin (candidate.timeBound x.length) config ∧
    (candidate.accepting
        (candidate.machine.run (candidate.timeBound x.length) config).state = true
      ↔ language x)

structure PolyDTMRealization (language : BitLanguage) where
  candidate : PolyDTMCandidate
  decides : ∀ x : BitString, candidate.CorrectAt language x

/-- Hardened nondeterministic candidate with the same finite/canonical model. -/
structure PolyNTMCandidate where
  stateCount : Nat
  machine : NTM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def PolyNTMCandidate.CorrectAt
    (candidate : PolyNTMCandidate)
    (language : BitLanguage)
    (x : BitString) : Prop :=
  let config := initialNTMConfig candidate.machine x
  candidate.machine.HaltsWithin (candidate.timeBound x.length) config ∧
    (candidate.machine.AcceptsWithin (candidate.timeBound x.length) config
      ↔ language x)

structure PolyNTMRealization (language : BitLanguage) where
  candidate : PolyNTMCandidate
  decides : ∀ x : BitString, candidate.CorrectAt language x

def InP (language : BitLanguage) : Prop :=
  Nonempty (PolyDTMRealization language)

def InNP (language : BitLanguage) : Prop :=
  Nonempty (PolyNTMRealization language)

def PneqNP : Prop :=
  ¬ ∀ language : BitLanguage, InP language ↔ InNP language

/-- Operational fail proof for one fixed language:
    every finite-control deterministic polynomial-time candidate has a concrete
    bitstring input on which it fails. -/
def UniversalFailure (language : BitLanguage) : Prop :=
  ∀ candidate : PolyDTMCandidate,
    ∃ x : BitString, ¬ candidate.CorrectAt language x

theorem universal_failure_implies_not_in_p
    {language : BitLanguage}
    (hFail : UniversalFailure language) :
    ¬ InP language := by
  intro hP
  rcases hP with ⟨realization⟩
  rcases hFail realization.candidate with ⟨x, hBad⟩
  exact hBad (realization.decides x)

theorem not_in_p_implies_universal_failure
    {language : BitLanguage}
    (hNotP : ¬ InP language) :
    UniversalFailure language := by
  intro candidate
  apply Classical.byContradiction
  intro hNoFailure
  apply hNotP
  refine ⟨{ candidate := candidate, decides := ?_ }⟩
  intro x
  apply Classical.byContradiction
  intro hBad
  exact hNoFailure ⟨x, hBad⟩

theorem universal_failure_iff_not_in_p
    {language : BitLanguage} :
    UniversalFailure language ↔ ¬ InP language := by
  constructor
  · exact universal_failure_implies_not_in_p
  · exact not_in_p_implies_universal_failure

/-- One genuine NP language plus a universal deterministic fail proof is exactly
    enough to separate the two machine classes. -/
theorem target_failure_implies_p_ne_np
    {language : BitLanguage}
    (hNP : InNP language)
    (hFail : UniversalFailure language) :
    PneqNP := by
  intro hEq
  have hP : InP language :=
    (hEq language).mpr hNP
  exact (universal_failure_implies_not_in_p hFail) hP

/-- Hardened endpoint payload. The target language is explicit rather than
    assumed to be SAT until a certified bitstring SAT encoding is supplied. -/
structure SeparationCertificate where
  target : BitLanguage
  target_in_np : InNP target
  fail_proof : UniversalFailure target

theorem separation_certificate_closes
    (cert : SeparationCertificate) :
    PneqNP :=
  target_failure_implies_p_ne_np cert.target_in_np cert.fail_proof

#print axioms MCore.Real.CanonicalFinalProof.universal_failure_implies_not_in_p
#print axioms MCore.Real.CanonicalFinalProof.not_in_p_implies_universal_failure
#print axioms MCore.Real.CanonicalFinalProof.universal_failure_iff_not_in_p
#print axioms MCore.Real.CanonicalFinalProof.target_failure_implies_p_ne_np
#print axioms MCore.Real.CanonicalFinalProof.separation_certificate_closes

end CanonicalFinalProof
end Real
end MCore
