import MCore.Real.CanonicalSATNTMAttack
import MCore.Real.P01RecursiveFiniteControlFrontier

namespace MCore
namespace Real
namespace P01FinalCertificate

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open CanonicalSATNTMAttack

/-!
P01 HARD final-certificate scaffold.

This file does not manufacture CanonicalSATMachineClosure and does not assume
the endpoint.  It isolates the exact concrete machine payload which must be
inhabited before P01 can be promoted.

Canonical model only:
* input: BitString = List Bool;
* tape alphabet: Option Bool;
* blank: none;
* finite control: Fin (stateCount + 1);
* no arbitrary input encoder;
* no Circuit/CNF value stored in control state;
* no hidden classical precomputation in initialization.

The remaining implementation is the single integrated NTM:
  parse -> nondeterministically choose witness -> verify -> accept/reject.
-/

/-- Exact machine-level payload still required for P01 HARD.

An inhabitant must provide the concrete finite-control NTM and prove its
polynomial bound, total halting, and semantic correctness on every BitString.
No endpoint proposition occurs as a field. -/
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

/-- Package a completed concrete construction into the hardened canonical
candidate type. -/
def P01MachineConstruction.toCandidate
    (C : P01MachineConstruction) :
    PolyNTMCandidate :=
  { stateCount := C.stateCount
    machine := C.machine
    blank_none := C.blank_none
    timeBound := C.timeBound
    time_poly := C.time_poly }

/-- The two machine obligations are exactly CorrectAt for the canonical SAT
bit-language. -/
theorem P01MachineConstruction.correctAt
    (C : P01MachineConstruction)
    (bs : BitString) :
    C.toCandidate.CorrectAt
      (SATBits circuitBitEncoding) bs := by
  constructor
  · exact C.halts bs
  · exact C.accepts_iff bs

/-- A completed construction yields the exact PolyNTMRealization required by
SATInNPGap. -/
def P01MachineConstruction.toRealization
    (C : P01MachineConstruction) :
    PolyNTMRealization (SATBits circuitBitEncoding) :=
  { candidate := C.toCandidate
    decides := C.correctAt }

/-- This is the only open implementation payload represented by this scaffold.
It is intentionally weaker than declaring the endpoint itself as an axiom or
premise. -/
def P01ConstructionGap : Prop :=
  Nonempty P01MachineConstruction

/-- Promotion theorem: once the concrete integrated machine construction exists,
it closes the existing P01 HARD endpoint without changing the endpoint
definition. -/
theorem construction_closes_p01
    (h : P01ConstructionGap) :
    CanonicalSATMachineClosure := by
  rcases h with ⟨C⟩
  exact ⟨C.toRealization⟩

/-
A future no-hypothesis final promotion theorem must construct a concrete
P01MachineConstruction and discharge construction_closes_p01.

Until that concrete inhabitant is constructed, P01 HARD remains OPEN.
-/

#print axioms MCore.Real.P01FinalCertificate.P01MachineConstruction.correctAt
#print axioms MCore.Real.P01FinalCertificate.construction_closes_p01

end P01FinalCertificate
end Real
end MCore
