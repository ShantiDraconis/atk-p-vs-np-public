import MCore.Real.CanonicalSATParserMachine
import MCore.Real.CanonicalSATSlotParserSpec
import MCore.Real.CanonicalSATParserAttack

namespace MCore
namespace Real
namespace CanonicalSATRecursiveParserSimulation

open CanonicalFinalProof
open CanonicalSATParserAttack
open CanonicalSATSlotParserSpec
open CanonicalSATParserMachine

/--
Exact remaining proof payload for the canonical Fin 25 parser machine.
No parallel parser model is introduced here.

The machine-specific semantic obligation is only realization of slotAccept;
slotAccept <-> decodeCircuit is already isolated in CanonicalSATSlotParserSpec.
-/
structure SlotParserMachineSimulationCertificate where
  halts :
    ∀ bits : BitString,
      parserMachine.HaltsWithin
        (parserTimeBound bits.length)
        (initialTMConfig parserMachine bits)

  realizes_slotAccept :
    ∀ bits : BitString,
      parserAccepting
          (parserMachine.run
            (parserTimeBound bits.length)
            (initialTMConfig parserMachine bits)).state = true
        ↔
      slotAccept bits = true

theorem simulation_correct
    (S : SlotParserMachineSimulationCertificate) :
    ∀ bits : BitString,
      parserAccepting
          (parserMachine.run
            (parserTimeBound bits.length)
            (initialTMConfig parserMachine bits)).state = true
        ↔
      ∃ c : CircuitK1.Circuit,
        CanonicalCircuitBits.decodeCircuit bits = some c := by
  intro bits
  exact
    (S.realizes_slotAccept bits).trans
      (slotAccept_iff_decodeCircuit bits)

/-- The exact hardened parser certificate induced by the Fin31 simulation. -/
def SlotParserMachineSimulationCertificate.toCanonicalCertificate
    (S : SlotParserMachineSimulationCertificate) :
    CanonicalRecursiveParserMachineCertificate :=
  { stateCount := 24
    machine := parserMachine
    blank_none := rfl
    accepting := parserAccepting
    timeBound := parserTimeBound
    time_poly := parserTimeBound_poly
    halts := S.halts
    correct := simulation_correct S }

theorem simulation_closes_operational_gap
    (S : SlotParserMachineSimulationCertificate) :
    CanonicalRecursiveParserOperationalGap := by
  exact ⟨S.toCanonicalCertificate⟩

def ParserSimulationGap : Prop :=
  Nonempty SlotParserMachineSimulationCertificate

theorem parserSimulationGap_closes
    (h : ParserSimulationGap) :
    CanonicalRecursiveParserOperationalGap := by
  rcases h with ⟨S⟩
  exact simulation_closes_operational_gap S

#print axioms MCore.Real.CanonicalSATRecursiveParserSimulation.simulation_correct
#print axioms MCore.Real.CanonicalSATRecursiveParserSimulation.simulation_closes_operational_gap
#print axioms MCore.Real.CanonicalSATRecursiveParserSimulation.parserSimulationGap_closes

end CanonicalSATRecursiveParserSimulation
end Real
end MCore
