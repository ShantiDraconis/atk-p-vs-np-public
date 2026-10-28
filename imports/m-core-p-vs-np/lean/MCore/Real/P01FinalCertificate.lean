import MCore.Real.CanonicalSATNTMAttack

namespace MCore
namespace Real
namespace P01FinalCertificate

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open CanonicalSATNTMAttack

/-- Exact concrete integrated NTM payload required for the SAT-in-NP side.
No endpoint proposition is stored as a field. -/
structure P01MachineConstruction where
  stateCount : Nat
  machine : NTM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts :
    ∀ bs : BitString,
      machine.HaltsWithin
        (timeBound bs.length)
        (initialNTMConfig machine bs)
  accepts_iff :
    ∀ bs : BitString,
      machine.AcceptsWithin
          (timeBound bs.length)
          (initialNTMConfig machine bs) ↔
        SATBits circuitBitEncoding bs

def P01MachineConstruction.toCandidate
    (C : P01MachineConstruction) :
    PolyNTMCandidate :=
  { stateCount := C.stateCount
    machine := C.machine
    blank_none := C.blank_none
    timeBound := C.timeBound
    time_poly := C.time_poly }

theorem P01MachineConstruction.correctAt
    (C : P01MachineConstruction)
    (bs : BitString) :
    C.toCandidate.CorrectAt
      (SATBits circuitBitEncoding) bs := by
  constructor
  · exact C.halts bs
  · exact C.accepts_iff bs

def P01MachineConstruction.toRealization
    (C : P01MachineConstruction) :
    PolyNTMRealization (SATBits circuitBitEncoding) :=
  { candidate := C.toCandidate
    decides := C.correctAt }

def P01ConstructionGap : Prop :=
  Nonempty P01MachineConstruction

theorem construction_closes_p01
    (h : P01ConstructionGap) :
    CanonicalSATMachineClosure := by
  rcases h with ⟨C⟩
  exact ⟨C.toRealization⟩

#print axioms MCore.Real.P01FinalCertificate.P01MachineConstruction.correctAt
#print axioms MCore.Real.P01FinalCertificate.construction_closes_p01

end P01FinalCertificate
end Real
end MCore
