import MCore.Real.CanonicalSATSlotLog
import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace CanonicalSATSlotLogMachine

open CanonicalFinalProof
open CanonicalSATSlotLog

/-- Work-region configuration.  The left pre is arbitrary parser data plus
its blank delimiter.  The head is the first slot-log cell, or blank for an
empty log. -/
def workConfig
    {n : Nat}
    (q : Fin n)
    (pre : List (Option Bool))
    (log : SlotLog) :
    Configuration (Fin n) (Option Bool) :=
  match log with
  | [] =>
      { state := q
        tape := { left := pre, head := none, right := [] } }
  | b :: bs =>
      { state := q
        tape := { left := pre, head := some b, right := bs.map some } }

@[simp] theorem workConfig_state
    {n : Nat}
    (q : Fin n)
    (pre : List (Option Bool))
    (log : SlotLog) :
    (workConfig q pre log).state = q := by
  cases log <;> rfl

/-- Two-state append machine. State 0 scans to the first blank after the work
log; state 1 halts after writing one active-slot cell. -/
def pushSlotMachine : TM (Fin 2) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some b => (0, some b, .right)
        | none => (1, some true, .stay)
      else
        (1, symbol, .stay)
    halting := fun q => q == 1 }

@[simp] theorem push_not_halted :
    pushSlotMachine.halting (0 : Fin 2) = false := rfl

@[simp] theorem push_halted :
    pushSlotMachine.halting (1 : Fin 2) = true := rfl

theorem push_step_cons
    (pre : List (Option Bool))
    (b : Bool)
    (bs : SlotLog) :
    pushSlotMachine.step (workConfig 0 pre (b :: bs)) =
      workConfig 0 (some b :: pre) bs := by
  cases bs <;>
    simp [pushSlotMachine, workConfig, TM.step, Tape.write, Tape.move]

theorem push_step_nil
    (pre : List (Option Bool)) :
    pushSlotMachine.step (workConfig 0 pre []) =
      { state := (1 : Fin 2)
        tape := { left := pre, head := some true, right := [] } } := by
  simp [pushSlotMachine, workConfig, TM.step, Tape.write, Tape.move]

/-- Exact append behavior.  The machine runs one step per old log cell plus
one write step. -/
theorem push_run
    (pre : List (Option Bool))
    (log : SlotLog) :
    let final :=
      pushSlotMachine.run (log.length + 1) (workConfig 0 pre log)
    final.state = (1 : Fin 2) ∧
      final.tape.right = [] ∧
      final.tape.head = some true := by
  induction log generalizing pre with
  | nil =>
      rw [TM.run, workConfig_state, push_not_halted]
      rw [push_step_nil]
      simp [TM.run, pushSlotMachine]
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show Nat.succ bs.length + 1 = (bs.length + 1) + 1 by omega]
      rw [TM.run, workConfig_state, push_not_halted]
      rw [push_step_cons]
      exact ih (some b :: pre)

/--
Four-state pop machine.
0 scans right to the blank after the log.
1 scans left over false tombstones.
2 success: rightmost active true was changed to false.
3 reject: no active true exists.
-/
def popSlotMachine : TM (Fin 4) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some b => (0, some b, .right)
        | none => (1, none, .left)
      else if q = 1 then
        match symbol with
        | some false => (1, some false, .left)
        | some true => (2, some false, .stay)
        | none => (3, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => (q == 2) || (q == 3) }

@[simp] theorem pop_not_halted_0 :
    popSlotMachine.halting (0 : Fin 4) = false := by decide
@[simp] theorem pop_not_halted_1 :
    popSlotMachine.halting (1 : Fin 4) = false := by decide
@[simp] theorem pop_halted_2 :
    popSlotMachine.halting (2 : Fin 4) = true := by decide
@[simp] theorem pop_halted_3 :
    popSlotMachine.halting (3 : Fin 4) = true := by decide

/-- Conservative work-log runtime: one right scan, one left scan, plus boundary
steps. -/
def slotLogTimeBound : TimeBound :=
  fun n => 2 * n + 3

theorem slotLogTimeBound_poly :
    PolynomialTimeBound slotLogTimeBound := by
  refine ⟨5, 1, ?_⟩
  intro n
  simp [slotLogTimeBound]
  omega

/-- Semantic consequence needed by the parser: push changes represented slot
count by +1, independent of physical parser pre. -/
theorem push_semantic
    {slots : Nat}
    {log : SlotLog}
    (h : RepresentsSlots slots log) :
    RepresentsSlots (slots + 1) (pushSlot log) :=
  pushSlot_represents h

/-- Semantic consequence needed by the parser: a successful pop changes a
positive represented count by exactly -1. -/
theorem pop_semantic
    {slots : Nat}
    {log log' : SlotLog}
    (hslots : RepresentsSlots (slots + 1) log)
    (hpop : popSlot log = some log') :
    RepresentsSlots slots log' :=
  popSlot_represents hslots hpop

#print axioms MCore.Real.CanonicalSATSlotLogMachine.push_step_cons
#print axioms MCore.Real.CanonicalSATSlotLogMachine.push_run
#print axioms MCore.Real.CanonicalSATSlotLogMachine.slotLogTimeBound_poly
#print axioms MCore.Real.CanonicalSATSlotLogMachine.push_semantic
#print axioms MCore.Real.CanonicalSATSlotLogMachine.pop_semantic

end CanonicalSATSlotLogMachine
end Real
end MCore
