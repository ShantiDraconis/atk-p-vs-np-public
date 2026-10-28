import MCore.Real.CanonicalSATRecursiveParserSimulation
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace CanonicalSATParserNTM

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATParserMachine
open CanonicalSATSlotParserSpec
open CanonicalSATRecursiveParserSimulation

/-- Generic singleton-branch embedding of a deterministic machine into an NTM.
    The tape alphabet, blank symbol and transition table are reused verbatim. -/
def tmAsSingletonNTM
    {State Symbol : Type}
    (tm : TM State Symbol)
    (accepting rejecting : State → Bool) :
    NTM State Symbol :=
  { initial := tm.initial
    blank := tm.blank
    transition := fun q symbol => [tm.transition q symbol]
    accepting := accepting
    rejecting := rejecting }

theorem tmAsSingletonNTM_stepBranch
    {State Symbol : Type}
    (tm : TM State Symbol)
    (accepting rejecting : State → Bool)
    (config : Configuration State Symbol) :
    (tmAsSingletonNTM tm accepting rejecting).stepBranch config
        (tm.transition config.state config.tape.head) =
      tm.step config := by
  rcases htr : tm.transition config.state config.tape.head with
    ⟨q, symbol, direction⟩
  simp [tmAsSingletonNTM, NTM.stepBranch, TM.step, htr]

/-- Deterministic parser embedded as a singleton-branch NTM.
    This introduces no second parser semantics: every active NTM step is
    exactly one step of parserMachine. -/
def parserNTM : NTM (Fin 25) (Option Bool) :=
  tmAsSingletonNTM parserMachine parserAccepting (fun q => q == 24)

@[simp] theorem parserNTM_blank_none :
    parserNTM.blank = none := by
  exact parserMachine_blank_none

@[simp] theorem parserNTM_initial :
    parserNTM.initial = (0 : Fin 25) := rfl

@[simp] theorem parserNTM_terminal_eq_parser_halt
    (q : Fin 25) :
    (parserNTM.accepting q || parserNTM.rejecting q) =
      parserMachine.halting q := by
  rfl

theorem parserNTM_stepBranch_eq_parser_step
    (config : Configuration (Fin 25) (Option Bool)) :
    parserNTM.stepBranch config
        (parserMachine.transition config.state config.tape.head) =
      parserMachine.step config := by
  exact
    tmAsSingletonNTM_stepBranch
      parserMachine parserAccepting (fun q => q == 24) config

theorem parserNTM_successors_singleton
    (config : Configuration (Fin 25) (Option Bool)) :
    parserNTM.successors config = [parserMachine.step config] := by
  rcases htr :
      parserMachine.transition config.state config.tape.head with
    ⟨q, symbol, direction⟩
  have hstep :
      parserNTM.stepBranch config (q, symbol, direction) =
        parserMachine.step config := by
    have h := parserNTM_stepBranch_eq_parser_step config
    rw [htr] at h
    exact h
  unfold NTM.successors
  have htrans :
      parserNTM.transition config.state config.tape.head =
        [(q, symbol, direction)] := by
    simp [parserNTM, tmAsSingletonNTM, htr]
  rw [htrans]
  simp only [List.map_cons, List.map_nil]
  rw [hstep]

/-- Singleton-branch execution is extensionally identical to deterministic
    parserMachine.run, including preservation of halted configurations. -/
theorem parserNTM_runBranches_singleton
    (fuel : Nat)
    (config : Configuration (Fin 25) (Option Bool)) :
    parserNTM.runBranches fuel [config] =
      [parserMachine.run fuel config] := by
  induction fuel generalizing config with
  | zero =>
      rfl
  | succ fuel ih =>
      cases hhalt : parserMachine.halting config.state with
      | false =>
          simp [NTM.runBranches, parserNTM_terminal_eq_parser_halt,
            hhalt, parserNTM_successors_singleton, TM.run, ih]
      | true =>
          have hrunFuel :
              parserMachine.run fuel config = config :=
            MachineRunLemmas.run_halted parserMachine config hhalt fuel
          have hrunSucc :
              parserMachine.run (fuel + 1) config = config :=
            MachineRunLemmas.run_halted parserMachine config hhalt (fuel + 1)
          simp [NTM.runBranches, parserNTM_terminal_eq_parser_halt,
            hhalt, ih, hrunFuel, hrunSucc]

theorem parserNTM_haltsWithin_iff
    (fuel : Nat)
    (config : Configuration (Fin 25) (Option Bool)) :
    parserNTM.HaltsWithin fuel config ↔
      parserMachine.HaltsWithin fuel config := by
  unfold NTM.HaltsWithin TM.HaltsWithin
  rw [parserNTM_runBranches_singleton]
  constructor
  · intro h
    have hterm :=
      h (parserMachine.run fuel config) (by simp)
    rcases hterm with hacc | hrej
    · have hor :
          (parserNTM.accepting (parserMachine.run fuel config).state ||
            parserNTM.rejecting (parserMachine.run fuel config).state) = true := by
          simp [hacc]
      rw [parserNTM_terminal_eq_parser_halt] at hor
      exact hor
    · have hor :
          (parserNTM.accepting (parserMachine.run fuel config).state ||
            parserNTM.rejecting (parserMachine.run fuel config).state) = true := by
          simp [hrej]
      rw [parserNTM_terminal_eq_parser_halt] at hor
      exact hor
  · intro h reached hmem
    simp only [List.mem_singleton] at hmem
    subst reached
    have hor :
        (parserNTM.accepting (parserMachine.run fuel config).state ||
          parserNTM.rejecting (parserMachine.run fuel config).state) = true := by
      rw [parserNTM_terminal_eq_parser_halt]
      exact h
    cases hacc : parserNTM.accepting (parserMachine.run fuel config).state <;>
      cases hrej : parserNTM.rejecting (parserMachine.run fuel config).state <;>
      simp_all

theorem parserNTM_acceptsWithin_iff
    (fuel : Nat)
    (config : Configuration (Fin 25) (Option Bool)) :
    parserNTM.AcceptsWithin fuel config ↔
      parserAccepting (parserMachine.run fuel config).state = true := by
  unfold NTM.AcceptsWithin
  rw [parserNTM_runBranches_singleton]
  constructor
  · rintro ⟨reached, hmem, hacc⟩
    simp only [List.mem_singleton] at hmem
    subst reached
    exact hacc
  · intro hacc
    exact ⟨parserMachine.run fuel config, by simp, hacc⟩

/-- A completed Fin-25 parser simulation can be reused directly as the parser
    phase of an integrated canonical NTM. -/
structure ParserNTMPhaseCertificate where
  halts :
    ∀ bits : BitString,
      parserNTM.HaltsWithin
        (parserTimeBound bits.length)
        (initialNTMConfig parserNTM bits)
  accepts_iff_decode :
    ∀ bits : BitString,
      parserNTM.AcceptsWithin
          (parserTimeBound bits.length)
          (initialNTMConfig parserNTM bits) ↔
        ∃ c : CircuitK1.Circuit,
          decodeCircuit bits = some c

def simulationToNTMPhase
    (S : SlotParserMachineSimulationCertificate) :
    ParserNTMPhaseCertificate := by
  refine
    { halts := ?_
      accepts_iff_decode := ?_ }
  · intro bits
    rw [parserNTM_haltsWithin_iff]
    exact S.halts bits
  · intro bits
    rw [parserNTM_acceptsWithin_iff]
    exact
      (S.realizes_slotAccept bits).trans
        (slotAccept_iff_decodeCircuit bits)

theorem parserSimulationGap_to_ntm_phase
    (h : ParserSimulationGap) :
    Nonempty ParserNTMPhaseCertificate := by
  rcases h with ⟨S⟩
  exact ⟨simulationToNTMPhase S⟩

#print axioms MCore.Real.CanonicalSATParserNTM.parserNTM_runBranches_singleton
#print axioms MCore.Real.CanonicalSATParserNTM.parserNTM_haltsWithin_iff
#print axioms MCore.Real.CanonicalSATParserNTM.parserNTM_acceptsWithin_iff
#print axioms MCore.Real.CanonicalSATParserNTM.simulationToNTMPhase
#print axioms MCore.Real.CanonicalSATParserNTM.parserSimulationGap_to_ntm_phase

end CanonicalSATParserNTM
end Real
end MCore
