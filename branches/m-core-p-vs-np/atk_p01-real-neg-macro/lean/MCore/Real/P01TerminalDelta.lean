import MCore.Real.P01ParserWitnessComposition
import MCore.Real.P01FullVerifierPhysical
import MCore.Real.P01PhysicalRealizationAssembly
import MCore.Real.P01IntegratedMachine
import MCore.Real.P01IntegratedPhaseSemantics
import MCore.Real.P01FinalCertificate

namespace MCore
namespace Real
namespace P01TerminalDelta

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P01FinalCertificate
open P01IntegratedMachine

/-- All reusable P01 components are already fixed and certified.  The only
remaining payload is the single integrated canonical NTM execution. -/
abbrev TerminalState := IntegratedState

/-- Exact executable payload still missing after parser/witness/verifier reuse.
This does not weaken P01MachineConstruction: it is merely the same terminal
machine data with the already-fixed state-space made explicit. -/
structure IntegratedExecutionCertificate where
  machine : NTM TerminalState (Option Bool)
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

/-- No semantic adapter is left after this point: an integrated execution
certificate is literally a P01MachineConstruction with stateCount = 46. -/
def IntegratedExecutionCertificate.toP01
    (C : IntegratedExecutionCertificate) :
    P01MachineConstruction where
  stateCount := 46
  machine := C.machine
  blank_none := C.blank_none
  timeBound := C.timeBound
  time_poly := C.time_poly
  halts := C.halts
  accepts_iff := C.accepts_iff

def P01TerminalGap : Prop :=
  Nonempty IntegratedExecutionCertificate

theorem p01_terminal_gap_closes
    (h : P01TerminalGap) :
    SATInNPGap circuitBitEncoding := by
  rcases h with ⟨C⟩
  exact construction_closes_p01 ⟨C.toP01⟩

/-- Certified reusable inputs for the final integrated implementation. -/
def parserPhase :=
  P01ParserWitnessComposition.parserPhaseCertificate

def phaseLayout :=
  P01IntegratedPhaseSemantics.canonicalPhaseLayoutCertificate

def phaseBridge :=
  P01IntegratedMachine.integratedPhaseBridgeCertificate

#print axioms MCore.Real.P01TerminalDelta.p01_terminal_gap_closes
#print axioms MCore.Real.P01TerminalDelta.parserPhase
#print axioms MCore.Real.P01TerminalDelta.phaseLayout
#print axioms MCore.Real.P01TerminalDelta.phaseBridge

end P01TerminalDelta
end Real
end MCore
