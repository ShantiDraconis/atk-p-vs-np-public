import MCore.Real.P01WitnessIndexedReadProof
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01WitnessIndexedReadGlobal

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01WitnessIndexedRead
open P01WitnessIndexedReadMachine
open P01WitnessIndexedReadProof
open MachineRunLemmas

@[simp] theorem witnessIndexedReadMachine_not_halt1 :
    witnessIndexedReadMachine.halting (1 : Fin 6) = false := by
  decide

@[simp] theorem witnessIndexedReadMachine_not_halt2 :
    witnessIndexedReadMachine.halting (2 : Fin 6) = false := by
  decide

/-- State-2 configuration positioned on the next unary index marker. -/
def markerConfig
    (pad : Nat) (witness : BitString) :
    Nat → Configuration (Fin 6) (Option Bool)
  | 0 =>
      { state := 2
        tape :=
          { left := List.replicate pad none ++ witness.map some
            head := some false
            right := [] } }
  | n + 1 =>
      { state := 2
        tape :=
          { left := List.replicate pad none ++ witness.map some
            head := some true
            right := (encodeNat n).map some } }

/-- State-1 configuration while crossing blank padding toward the witness cell
that will be consumed for one unary true marker. -/
def eraseSeekConfig
    (pad extra : Nat) (b : Bool) (tail : BitString) (n : Nat) :
    Configuration (Fin 6) (Option Bool) :=
  match pad with
  | 0 =>
      { state := 1
        tape :=
          { left := tail.map some
            head := some b
            right :=
              List.replicate (extra + 1) none ++ (encodeNat n).map some } }
  | k + 1 =>
      { state := 1
        tape :=
          { left := List.replicate k none ++ some b :: tail.map some
            head := none
            right :=
              List.replicate (extra + 1) none ++ (encodeNat n).map some } }

/-- State-2 configuration while scanning right across erased blank cells back
to the remaining unary index. -/
def rightScanConfig
    (leftPad rightPad : Nat) (tail : BitString) (n : Nat) :
    Configuration (Fin 6) (Option Bool) :=
  { state := 2
    tape :=
      { left := List.replicate leftPad none ++ tail.map some
        head := none
        right := List.replicate rightPad none ++ (encodeNat n).map some } }

@[simp] theorem markerConfig_state
    (pad : Nat) (witness : BitString) (n : Nat) :
    (markerConfig pad witness n).state = (2 : Fin 6) := by
  cases n <;> rfl

@[simp] theorem eraseSeekConfig_state
    (pad extra : Nat) (b : Bool) (tail : BitString) (n : Nat) :
    (eraseSeekConfig pad extra b tail n).state = (1 : Fin 6) := by
  cases pad <;> rfl

@[simp] theorem rightScanConfig_state
    (leftPad rightPad : Nat) (tail : BitString) (n : Nat) :
    (rightScanConfig leftPad rightPad tail n).state = (2 : Fin 6) := rfl

theorem marker_succ_step
    (pad n : Nat) (b : Bool) (tail : BitString) :
    witnessIndexedReadMachine.step
      (markerConfig pad (b :: tail) (n + 1)) =
      eraseSeekConfig pad 0 b tail n := by
  cases pad <;>
    simp [markerConfig, eraseSeekConfig, encodeNat,
      witnessIndexedReadMachine, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

theorem eraseSeek_step_succ
    (pad extra n : Nat) (b : Bool) (tail : BitString) :
    witnessIndexedReadMachine.step
      (eraseSeekConfig (pad + 1) extra b tail n) =
      eraseSeekConfig pad (extra + 1) b tail n := by
  cases pad <;>
    simp [eraseSeekConfig, witnessIndexedReadMachine, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem eraseSeek_run
    (pad extra n : Nat) (b : Bool) (tail : BitString) :
    witnessIndexedReadMachine.run (pad + 1)
      (eraseSeekConfig pad extra b tail n) =
      rightScanConfig 1 (pad + extra) tail n := by
  induction pad generalizing extra with
  | zero =>
      simp only [Nat.zero_add]
      simp [eraseSeekConfig, rightScanConfig, witnessIndexedReadMachine,
        TM.run, TM.step, Tape.write]
      rw [show extra + 1 = Nat.succ extra by omega, List.replicate_succ]
      rfl
  | succ pad ih =>
      rw [show Nat.succ pad + 1 = (pad + 1) + 1 by omega]
      rw [TM.run]
      rw [eraseSeekConfig_state]
      rw [witnessIndexedReadMachine_not_halt1]
      rw [eraseSeek_step_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ih (extra := extra + 1))

theorem rightScan_step_succ
    (leftPad rightPad n : Nat) (tail : BitString) :
    witnessIndexedReadMachine.step
      (rightScanConfig leftPad (rightPad + 1) tail n) =
      rightScanConfig (leftPad + 1) rightPad tail n := by
  simp [rightScanConfig, witnessIndexedReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem rightScan_run
    (leftPad rightPad n : Nat) (tail : BitString) :
    witnessIndexedReadMachine.run (rightPad + 1)
      (rightScanConfig leftPad rightPad tail n) =
      markerConfig (leftPad + rightPad + 1) tail n := by
  induction rightPad generalizing leftPad with
  | zero =>
      cases n <;>
        simp [rightScanConfig, markerConfig, encodeNat,
          witnessIndexedReadMachine, TM.run, TM.step, Tape.write, Tape.move,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;>
        rfl
  | succ rightPad ih =>
      rw [show Nat.succ rightPad + 1 = (rightPad + 1) + 1 by omega]
      rw [TM.run]
      rw [rightScanConfig_state]
      rw [witnessIndexedReadMachine_not_halt2]
      rw [rightScan_step_succ]
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        (ih (leftPad := leftPad + 1))

/-- One unary true marker consumes exactly one witness cell and advances to
the next index marker. -/
theorem marker_succ_run
    (pad n : Nat) (b : Bool) (tail : BitString) :
    witnessIndexedReadMachine.run (2 * pad + 3)
      (markerConfig pad (b :: tail) (n + 1)) =
      markerConfig (pad + 2) tail n := by
  have h1 :
      witnessIndexedReadMachine.run 1
        (markerConfig pad (b :: tail) (n + 1)) =
        eraseSeekConfig pad 0 b tail n := by
    rw [TM.run]
    rw [markerConfig_state]
    rw [witnessIndexedReadMachine_not_halt2]
    exact marker_succ_step pad n b tail
  have h2 := eraseSeek_run pad 0 n b tail
  have h3 := rightScan_run 1 pad n tail
  rw [show 2 * pad + 3 = 1 + ((pad + 1) + (pad + 1)) by omega]
  rw [run_add]
  rw [h1]
  rw [run_add]
  rw [h2]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h3

def markerFuel (pad n : Nat) : Nat :=
  pad * (2 * n + 1) + 2 * n^2 + 3 * n + 2

def readFuel (n : Nat) : Nat :=
  2 * n^2 + 5 * n + 3

theorem markerFuel_zero (pad : Nat) :
    markerFuel pad 0 = pad + 2 := by
  simp [markerFuel]

theorem markerFuel_succ (pad n : Nat) :
    markerFuel pad (n + 1) =
      (2 * pad + 3) + markerFuel (pad + 2) n := by
  unfold markerFuel
  simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
  omega

theorem readFuel_zero :
    readFuel 0 = 3 := by
  rfl

theorem readFuel_succ (n : Nat) :
    readFuel (n + 1) = 5 + markerFuel 3 n := by
  unfold readFuel markerFuel
  simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
  omega

theorem marker_zero_run_state
    (pad : Nat) (b : Bool) (tail : BitString) :
    (witnessIndexedReadMachine.run (markerFuel pad 0)
      (markerConfig pad (b :: tail) 0)).state =
      (if b then (4 : Fin 6) else (5 : Fin 6)) := by
  rw [markerFuel_zero]
  cases pad with
  | zero =>
      cases b <;>
        simp [markerConfig, witnessIndexedReadMachine, TM.run, TM.step,
          Tape.write, Tape.move]
  | succ pad =>
      have hstep :
          witnessIndexedReadMachine.step
            (markerConfig (Nat.succ pad) (b :: tail) 0) =
            witnessSeekConfig pad b tail [some false] := by
        simp [markerConfig, encodeNat, witnessSeekConfig,
          witnessIndexedReadMachine, TM.step, Tape.write, Tape.move,
          List.replicate_succ, List.append_assoc]
      rw [show Nat.succ pad + 2 = 1 + (pad + 2) by omega]
      rw [run_add]
      have hrun1 :
          witnessIndexedReadMachine.run 1
            (markerConfig (Nat.succ pad) (b :: tail) 0) =
            witnessSeekConfig pad b tail [some false] := by
        rw [TM.run]
        rw [markerConfig_state]
        rw [witnessIndexedReadMachine_not_halt2]
        exact hstep
      rw [hrun1]
      exact witnessSeek_run_state pad b tail [some false]

theorem marker_run_state
    (pad n : Nat) (witness : BitString)
    (h : n < witness.length) :
    (witnessIndexedReadMachine.run (markerFuel pad n)
      (markerConfig pad witness n)).state =
      (if witness.getD n false then (4 : Fin 6) else (5 : Fin 6)) := by
  induction n generalizing pad witness with
  | zero =>
      cases witness with
      | nil =>
          simp at h
      | cons b tail =>
          simpa using marker_zero_run_state pad b tail
  | succ n ih =>
      cases witness with
      | nil =>
          simp at h
      | cons b tail =>
          have htail : n < tail.length := by
            simpa using Nat.succ_lt_succ_iff.mp h
          rw [markerFuel_succ]
          rw [run_add]
          rw [marker_succ_run]
          simpa using ih (pad := pad + 2) (witness := tail) htail

theorem initial_succ_run_five
    (n : Nat) (b : Bool) (tail : BitString) :
    witnessIndexedReadMachine.run 5
      { state := witnessIndexedReadMachine.initial
        tape := witnessReadTape (b :: tail) (n + 1) } =
      markerConfig 3 tail n := by
  cases b <;> cases n <;>
    simp [witnessReadTape, markerConfig, encodeNat,
      witnessIndexedReadMachine, TM.run, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

theorem indexedRead_run_state
    (n : Nat) (witness : BitString)
    (h : n < witness.length) :
    (witnessIndexedReadMachine.run (readFuel n)
      { state := witnessIndexedReadMachine.initial
        tape := witnessReadTape witness n }).state =
      (if witness.getD n false then (4 : Fin 6) else (5 : Fin 6)) := by
  induction n generalizing witness with
  | zero =>
      cases witness with
      | nil =>
          simp at h
      | cons b tail =>
          cases b <;>
            simp [readFuel, read_zero_false, read_zero_true]
  | succ n ih =>
      cases witness with
      | nil =>
          simp at h
      | cons b tail =>
          have htail : n < tail.length := by
            simpa using Nat.succ_lt_succ_iff.mp h
          rw [readFuel_succ]
          rw [run_add]
          rw [initial_succ_run_five]
          simpa using marker_run_state 3 n tail htail

theorem indexedRead_halts_small
    (n : Nat) (witness : BitString)
    (h : n < witness.length) :
    witnessIndexedReadMachine.HaltsWithin (readFuel n)
      { state := witnessIndexedReadMachine.initial
        tape := witnessReadTape witness n } := by
  unfold TM.HaltsWithin
  rw [indexedRead_run_state n witness h]
  cases hbit : witness.getD n false <;>
    simp [witnessIndexedReadMachine]

theorem readFuel_le_timeBound
    (witness : BitString) (n : Nat) :
    readFuel n ≤
      witnessIndexedReadTimeBound
        (witness.length + (encodeNat n).length) := by
  simp [readFuel, witnessIndexedReadTimeBound,
    CanonicalSATWitness.encodeNat_length, Nat.pow_succ, Nat.mul_add, Nat.add_mul]
  omega

theorem witnessBits_getD
    {phi : CircuitK1.Circuit}
    (w : SATWitness phi) (i : Nat) (hi : i < varBound phi) :
    (witnessBits w).getD i false = w ⟨i, hi⟩ := by
  have hlen : i < (witnessBits w).length := by
    simpa [witnessBits_length] using hi
  rw [List.getD_eq_getElem?_getD]
  simp [witnessBits, List.getElem?_ofFn, hi]

def witnessIndexedReadCertificate : WitnessIndexedReadCertificate where
  stateCount := 5
  machine := witnessIndexedReadMachine
  blank_none := rfl
  accepting := witnessIndexedAccepting
  timeBound := witnessIndexedReadTimeBound
  time_poly := witnessIndexedReadTimeBound_poly
  halts := by
    intro phi w i hi
    have hlen : i < (witnessBits w).length := by
      simpa [witnessBits_length] using hi
    exact
      haltsWithin_mono witnessIndexedReadMachine
        { state := witnessIndexedReadMachine.initial
          tape := witnessReadTape (witnessBits w) i }
        (readFuel_le_timeBound (witnessBits w) i)
        (indexedRead_halts_small i (witnessBits w) hlen)
  correct := by
    intro phi w i hi
    have hlen : i < (witnessBits w).length := by
      simpa [witnessBits_length] using hi
    let cfg : Configuration (Fin 6) (Option Bool) :=
      { state := witnessIndexedReadMachine.initial
        tape := witnessReadTape (witnessBits w) i }
    have hsmall :
        witnessIndexedReadMachine.HaltsWithin (readFuel i) cfg := by
      simpa [cfg] using indexedRead_halts_small i (witnessBits w) hlen
    have hrun :
        witnessIndexedReadMachine.run
            (witnessIndexedReadTimeBound
              ((witnessBits w).length + (encodeNat i).length)) cfg =
          witnessIndexedReadMachine.run (readFuel i) cfg := by
      exact
        run_to_larger_fuel_of_halt witnessIndexedReadMachine cfg
          (witnessIndexedReadMachine.run (readFuel i) cfg)
          (readFuel_le_timeBound (witnessBits w) i)
          rfl hsmall
    rw [show
      ({ state := witnessIndexedReadMachine.initial
         tape := witnessReadTape (witnessBits w) i } :
        Configuration (Fin 6) (Option Bool)) = cfg by rfl]
    rw [hrun]
    have hstate := indexedRead_run_state i (witnessBits w) hlen
    rw [show
      (witnessIndexedReadMachine.run (readFuel i) cfg).state =
        (if (witnessBits w).getD i false then (4 : Fin 6) else (5 : Fin 6)) by
          simpa [cfg] using hstate]
    rw [witnessBits_getD w i hi]
    cases hbit : w ⟨i, hi⟩ <;>
      simp [witnessIndexedAccepting]

theorem witnessIndexedReadGap_closed :
    WitnessIndexedReadGap :=
  ⟨witnessIndexedReadCertificate⟩

#print axioms MCore.Real.P01WitnessIndexedReadGlobal.marker_run_state
#print axioms MCore.Real.P01WitnessIndexedReadGlobal.indexedRead_run_state
#print axioms MCore.Real.P01WitnessIndexedReadGlobal.witnessIndexedReadCertificate
#print axioms MCore.Real.P01WitnessIndexedReadGlobal.witnessIndexedReadGap_closed

end P01WitnessIndexedReadGlobal
end Real
end MCore
