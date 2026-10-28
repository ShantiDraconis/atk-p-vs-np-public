import MCore.Real.CanonicalSATParserAttack

namespace MCore
namespace Real
namespace CanonicalSATNatParserAttack

open CanonicalFinalProof
open CanonicalCircuitBits

/-- Three-state unary payload scanner for CanonicalCircuitBits.encodeNat.
    0 scans unary true bits, 1 accepts at the false terminator,
    2 rejects a truncated payload ending at blank. -/
def natScanMachine : TM (Fin 3) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some true  => (0, some true, .right)
        | some false => (1, some false, .stay)
        | none       => (2, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => (q == 1) || (q == 2) }

@[simp] theorem natScan_not_halted_zero :
    natScanMachine.halting (0 : Fin 3) = false := by
  decide

@[simp] theorem natScan_halted_one :
    natScanMachine.halting (1 : Fin 3) = true := by
  decide

@[simp] theorem natScan_halted_two :
    natScanMachine.halting (2 : Fin 3) = true := by
  decide

def natConfig
    (q : Fin 3)
    (left : List (Option Bool))
    (bits : BitString) :
    Configuration (Fin 3) (Option Bool) :=
  match bits with
  | [] =>
      { state := q
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := q
        tape := { left := left, head := some b, right := bs.map some } }

@[simp] theorem natConfig_state
    (q : Fin 3)
    (left : List (Option Bool))
    (bits : BitString) :
    (natConfig q left bits).state = q := by
  cases bits <;> rfl

theorem nat_step_true
    (left : List (Option Bool))
    (rest : BitString) :
    natScanMachine.step (natConfig 0 left (true :: rest)) =
      natConfig 0 (some true :: left) rest := by
  cases rest <;>
    simp [natScanMachine, natConfig, TM.step, Tape.write, Tape.move]

theorem nat_step_false
    (left : List (Option Bool))
    (rest : BitString) :
    natScanMachine.step (natConfig 0 left (false :: rest)) =
      natConfig 1 left (false :: rest) := by
  simp [natScanMachine, natConfig, TM.step, Tape.write, Tape.move]

theorem nat_step_blank_rejects
    (left : List (Option Bool)) :
    natScanMachine.step (natConfig 0 left []) =
      natConfig 2 left [] := by
  simp [natScanMachine, natConfig, TM.step, Tape.write, Tape.move]

theorem nat_run_encodeNat_state
    (left : List (Option Bool))
    (n : Nat)
    (tail : BitString) :
    (natScanMachine.run (n + 1)
      (natConfig 0 left (encodeNat n ++ tail))).state = (1 : Fin 3) := by
  induction n generalizing left with
  | zero =>
      simp only [encodeNat, List.cons_append]
      rw [TM.run, natConfig_state, natScan_not_halted_zero]
      rw [nat_step_false]
      simp [TM.run, natConfig]
  | succ n ih =>
      simp only [encodeNat, List.cons_append]
      rw [show Nat.succ n + 1 = (n + 1) + 1 by omega]
      rw [TM.run, natConfig_state, natScan_not_halted_zero]
      rw [nat_step_true]
      exact ih (some true :: left)

theorem nat_scan_encodeNat_halts_linear
    (n : Nat)
    (tail : BitString) :
    natScanMachine.HaltsWithin (n + 1)
      (natConfig 0 [] (encodeNat n ++ tail)) := by
  rw [TM.HaltsWithin]
  have hState := nat_run_encodeNat_state [] n tail
  rw [hState]
  exact natScan_halted_one

/-- Truncated unary payload fails immediately once blank is reached. -/
theorem nat_scan_blank_rejects :
    (natScanMachine.run 1 (natConfig 0 [] [])).state = (2 : Fin 3) := by
  rw [TM.run, natConfig_state, natScan_not_halted_zero]
  rw [nat_step_blank_rejects]
  simp [TM.run, natConfig]

/-- After fixed-tag recognition and unary-index scanning, the remaining parser
    frontier is recursive constructor-frame bookkeeping on the canonical tape. -/
structure RecursiveFrameMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def RecursiveFrameOperationalGap : Prop :=
  Nonempty RecursiveFrameMachineCertificate

#print axioms MCore.Real.CanonicalSATNatParserAttack.nat_step_true
#print axioms MCore.Real.CanonicalSATNatParserAttack.nat_step_false
#print axioms MCore.Real.CanonicalSATNatParserAttack.nat_step_blank_rejects
#print axioms MCore.Real.CanonicalSATNatParserAttack.nat_run_encodeNat_state
#print axioms MCore.Real.CanonicalSATNatParserAttack.nat_scan_encodeNat_halts_linear
#print axioms MCore.Real.CanonicalSATNatParserAttack.nat_scan_blank_rejects

end CanonicalSATNatParserAttack
end Real
end MCore
