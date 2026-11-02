import MCore.Real.CanonicalSATVerifier

namespace MCore
namespace Real
namespace CanonicalSATNTMAttack

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open CanonicalSATVerifier

/-- Canonical two-state tape scanner.
    State 0 scans right across input bits.
    State 1 is the halting state reached at the first blank. -/
def scanMachine : TM (Fin 2) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | none => (1, none, .stay)
        | some b => (0, some b, .right)
      else
        (1, symbol, .stay)
    halting := fun q => q == 1 }

/-- Generalized canonical scanning configuration; the left list is the already
    visited tape prefix in the tape's native reversed-left convention. -/
def scanConfig
    (left : List (Option Bool))
    (bits : BitString) :
    Configuration (Fin 2) (Option Bool) :=
  match bits with
  | [] =>
      { state := 0
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := 0
        tape := { left := left, head := some b, right := bs.map some } }

@[simp] theorem scanConfig_state
    (left : List (Option Bool))
    (bits : BitString) :
    (scanConfig left bits).state = (0 : Fin 2) := by
  cases bits <;> rfl

@[simp] theorem scanMachine_not_halted_at_zero :
    scanMachine.halting (0 : Fin 2) = false := by
  rfl

@[simp] theorem scanMachine_halted_at_one :
    scanMachine.halting (1 : Fin 2) = true := by
  rfl

theorem scan_step_cons
    (left : List (Option Bool))
    (b : Bool)
    (bs : BitString) :
    scanMachine.step (scanConfig left (b :: bs)) =
      scanConfig (some b :: left) bs := by
  cases bs <;>
    simp [scanMachine, scanConfig, TM.step, Tape.write, Tape.move]

theorem scan_step_nil
    (left : List (Option Bool)) :
    scanMachine.step (scanConfig left []) =
      { state := (1 : Fin 2),
        tape := { left := left, head := none, right := [] } } := by
  simp [scanMachine, scanConfig, TM.step, Tape.write, Tape.move]

theorem scan_run_reaches_halt
    (left : List (Option Bool))
    (bits : BitString) :
    scanMachine.halting
      (scanMachine.run (bits.length + 1) (scanConfig left bits)).state = true := by
  induction bits generalizing left with
  | nil =>
      change
        scanMachine.halting
          (scanMachine.run 1 (scanConfig left [])).state = true
      rw [TM.run]
      rw [scanConfig_state]
      rw [scanMachine_not_halted_at_zero]
      rw [scan_step_nil]
      exact scanMachine_halted_at_one
  | cons b bs ih =>
      rw [List.length_cons]
      rw [TM.run]
      rw [scanConfig_state]
      rw [scanMachine_not_halted_at_zero]
      rw [scan_step_cons]
      exact ih (some b :: left)

theorem scan_halts_within_linear
    (bits : BitString) :
    scanMachine.HaltsWithin (bits.length + 1)
      (initialTMConfig scanMachine bits) := by
  have hConfig :
      initialTMConfig scanMachine bits = scanConfig [] bits := by
    cases bits <;> rfl
  rw [hConfig]
  exact scan_run_reaches_halt [] bits

/-- The operational SAT bridge is decomposed into explicit machine-level
    obligations rather than hidden behind one opaque existence field. -/
structure ParserMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

structure WitnessGuessMachineCertificate where
  stateCount : Nat
  machine : NTM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

structure VerifierMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

/-- Exact remaining composition target: a concrete canonical NTM realization
    of SATBits. No inhabitant is postulated here. -/
def CanonicalSATMachineClosure : Prop :=
  CanonicalSATBoundary.SATInNPGap
    CanonicalCircuitBits.circuitBitEncoding

theorem canonical_sat_machine_closure_gives_bridge
    (h : CanonicalSATMachineClosure) :
    CanonicalSATOperationalGap := by
  exact ⟨{ realization := h }⟩

#print axioms MCore.Real.CanonicalSATNTMAttack.scan_step_cons
#print axioms MCore.Real.CanonicalSATNTMAttack.scan_step_nil
#print axioms MCore.Real.CanonicalSATNTMAttack.scan_run_reaches_halt
#print axioms MCore.Real.CanonicalSATNTMAttack.scan_halts_within_linear
#print axioms MCore.Real.CanonicalSATNTMAttack.canonical_sat_machine_closure_gives_bridge

end CanonicalSATNTMAttack
end Real
end MCore
