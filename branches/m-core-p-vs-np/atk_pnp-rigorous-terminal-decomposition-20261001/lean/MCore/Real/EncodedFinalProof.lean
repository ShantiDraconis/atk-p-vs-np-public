import MCore.Real.P01FinalCertificate
import MCore.Real.CanonicalCircuitBits

namespace MCore.Real
namespace EncodedFinalProof

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P01FinalCertificate

/-- The actual input length consumed by the canonical machine. -/
def EncodedCircuitSize (φ : Circuit) : Nat :=
  (encodeCircuit φ).length

/-- Deterministic candidates measured against the actual canonical encoding. -/
structure EncodedPolyDTMCandidate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def EncodedPolyDTMCandidate.CorrectAt
    (candidate : EncodedPolyDTMCandidate)
    (language : Circuit → Prop)
    (φ : Circuit) : Prop :=
  let cfg := initialTMConfig candidate.machine (encodeCircuit φ)
  candidate.machine.HaltsWithin
      (candidate.timeBound (EncodedCircuitSize φ)) cfg ∧
    (candidate.accepting
        (candidate.machine.run
          (candidate.timeBound (EncodedCircuitSize φ)) cfg).state = true
      ↔ language φ)

structure EncodedPolyDTMRealization (language : Circuit → Prop) where
  candidate : EncodedPolyDTMCandidate
  decides : ∀ φ, candidate.CorrectAt language φ

/-- Nondeterministic realization in the exact same encoded-size model. -/
structure EncodedPolyNTMRealization (language : Circuit → Prop) where
  stateCount : Nat
  machine : NTM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  decides :
    ∀ φ : Circuit,
      machine.HaltsWithin
          (timeBound (EncodedCircuitSize φ))
          (initialNTMConfig machine (encodeCircuit φ)) ∧
        (machine.AcceptsWithin
            (timeBound (EncodedCircuitSize φ))
            (initialNTMConfig machine (encodeCircuit φ))
          ↔ language φ)

def EncodedInP (language : Circuit → Prop) : Prop :=
  Nonempty (EncodedPolyDTMRealization language)

def EncodedInNP (language : Circuit → Prop) : Prop :=
  Nonempty (EncodedPolyNTMRealization language)

def EncodedMachinePneqNP : Prop :=
  ¬ ∀ language : Circuit → Prop, EncodedInP language ↔ EncodedInNP language

def EncodedSATInNP : Prop := EncodedInNP SATLanguage
def EncodedSATNotInP : Prop := ¬ EncodedInP SATLanguage

def EncodedUniversalSATFailure : Prop :=
  ∀ candidate : EncodedPolyDTMCandidate,
    ∃ φ : Circuit, ¬ candidate.CorrectAt SATLanguage φ

structure EncodedSATLowerBoundCertificate : Prop where
  fail_proof : EncodedUniversalSATFailure

theorem encoded_failure_implies_sat_not_in_p
    (h : EncodedUniversalSATFailure) :
    EncodedSATNotInP := by
  intro hP
  rcases hP with ⟨R⟩
  rcases h R.candidate with ⟨φ, hbad⟩
  exact hbad (R.decides φ)

theorem encoded_sat_boundary_implies_separation
    (hNP : EncodedSATInNP)
    (hLB : EncodedSATLowerBoundCertificate) :
    EncodedMachinePneqNP := by
  intro hEq
  have hP : EncodedInP SATLanguage :=
    (hEq SATLanguage).mpr hNP
  exact (encoded_failure_implies_sat_not_in_p hLB.fail_proof) hP

/-- P01 now closes the SAT-in-NP side with no size mismatch: both its runtime
    and this final model are indexed by the exact bitstring length. -/
def encodedSATInNP_of_P01
    (C : P01MachineConstruction) :
    EncodedSATInNP := by
  refine ⟨{
    stateCount := C.stateCount
    machine := C.machine
    blank_none := C.blank_none
    timeBound := C.timeBound
    time_poly := C.time_poly
    decides := ?_
  }⟩
  intro φ
  constructor
  · exact C.halts (encodeCircuit φ)
  · calc
      C.machine.AcceptsWithin
          (C.timeBound (EncodedCircuitSize φ))
          (initialNTMConfig C.machine (encodeCircuit φ))
          ↔ SATBits circuitBitEncoding (encodeCircuit φ) :=
        C.accepts_iff (encodeCircuit φ)
      _ ↔ SATLanguage φ := encoded_sat_equivalence φ

theorem encodedSATInNP_of_P01Gap
    (h : P01ConstructionGap) :
    EncodedSATInNP := by
  rcases h with ⟨C⟩
  exact encodedSATInNP_of_P01 C

structure RigorousFinalExternal : Prop where
  p01 : P01ConstructionGap
  lowerBound : EncodedSATLowerBoundCertificate

def RIGOROUS_FINAL_ROOT : Prop := EncodedMachinePneqNP

theorem rigorousFinalExternal_to_ROOT
    (E : RigorousFinalExternal) :
    RIGOROUS_FINAL_ROOT :=
  encoded_sat_boundary_implies_separation
    (encodedSATInNP_of_P01Gap E.p01)
    E.lowerBound

#print axioms MCore.Real.EncodedFinalProof.encodedSATInNP_of_P01
#print axioms MCore.Real.EncodedFinalProof.encodedSATInNP_of_P01Gap
#print axioms MCore.Real.EncodedFinalProof.rigorousFinalExternal_to_ROOT

end EncodedFinalProof
end MCore.Real
