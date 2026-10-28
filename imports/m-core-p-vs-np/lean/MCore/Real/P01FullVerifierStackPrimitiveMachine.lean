import MCore.Real.P01FullVerifierPhysicalStackV2

namespace MCore
namespace Real
namespace P01FullVerifierStackPrimitiveMachine

open CanonicalFinalProof
open P01FullVerifierPhysicalStackV2

/-- Fixed finite-control machine for exact stack push/pop on the V2 layout.
Entry states 0/1 push false/true; state 2 starts pop; state 3 reads popped bit.
States 4/5/6 are successful halts, state 7 is malformed-stack rejection. -/
abbrev StackState := Fin 8

def pushFalse : StackState := 0
def pushTrue : StackState := 1
def popStart : StackState := 2
def popRead : StackState := 3
def haltPush : StackState := 4
def haltPopFalse : StackState := 5
def haltPopTrue : StackState := 6
def reject : StackState := 7

def stackPrimitiveMachine : TM StackState (Option Bool) :=
  { initial := pushFalse
    blank := none
    transition := fun q symbol =>
      if q = pushFalse then
        match symbol with
        | none => (haltPush, some false, .right)
        | some b => (reject, some b, .stay)
      else if q = pushTrue then
        match symbol with
        | none => (haltPush, some true, .right)
        | some b => (reject, some b, .stay)
      else if q = popStart then
        match symbol with
        | none => (popRead, none, .left)
        | some b => (reject, some b, .stay)
      else if q = popRead then
        match symbol with
        | some false => (haltPopFalse, none, .stay)
        | some true => (haltPopTrue, none, .stay)
        | none => (reject, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q =>
      (q == haltPush) || (q == haltPopFalse) ||
        (q == haltPopTrue) || (q == reject) }

@[simp] theorem stackPrimitiveMachine_blank :
    stackPrimitiveMachine.blank = none := rfl

def pushConfig
    (b : Bool) (t : Tape (Option Bool)) :
    Configuration StackState (Option Bool) :=
  { state := if b then pushTrue else pushFalse, tape := t }

def popConfig
    (t : Tape (Option Bool)) :
    Configuration StackState (Option Bool) :=
  { state := popStart, tape := t }

theorem push_run_one
    (witness source : BitString)
    (stack : List Bool) (padding : Nat) (b : Bool) :
    (stackPrimitiveMachine.run 1
      (pushConfig b (physicalStackV2Tape witness source stack padding))).tape =
      pushStep b (physicalStackV2Tape witness source stack padding) := by
  cases b <;>
    simp [stackPrimitiveMachine, pushConfig, pushFalse, pushTrue, haltPush,
      haltPopFalse, haltPopTrue, reject, TM.run, TM.step, pushStep,
      physicalStackV2Tape, Tape.write, Tape.move]

theorem push_run_one_rep
    (witness source : BitString)
    (stack : List Bool) (padding : Nat) (b : Bool) :
    PhysicalStackRepV2
      (stackPrimitiveMachine.run 1
        (pushConfig b (physicalStackV2Tape witness source stack padding))).tape
      witness source (b :: stack) := by
  rw [push_run_one]
  exact physicalStackRepV2_push b ⟨padding, rfl⟩

theorem pop_run_two_false
    (witness source : BitString)
    (stack : List Bool) (padding : Nat) :
    let final := stackPrimitiveMachine.run 2
      (popConfig (physicalStackV2Tape witness source (false :: stack) padding))
    final.state = haltPopFalse /\
      PhysicalStackRepV2 final.tape witness source stack := by
  simp [stackPrimitiveMachine, popConfig, pushFalse, pushTrue, popStart, popRead,
    haltPush, haltPopFalse, haltPopTrue, reject, TM.run, TM.step,
    physicalStackV2Tape, Tape.write,
    Tape.move, PhysicalStackRepV2, List.map_cons, List.replicate_succ,
    Nat.add_comm]
  exact ⟨padding + 1, by
    simp [physicalStackV2Tape, List.replicate_succ, Nat.add_comm]⟩

theorem pop_run_two_true
    (witness source : BitString)
    (stack : List Bool) (padding : Nat) :
    let final := stackPrimitiveMachine.run 2
      (popConfig (physicalStackV2Tape witness source (true :: stack) padding))
    final.state = haltPopTrue /\
      PhysicalStackRepV2 final.tape witness source stack := by
  simp [stackPrimitiveMachine, popConfig, pushFalse, pushTrue, popStart, popRead,
    haltPush, haltPopFalse, haltPopTrue, reject, TM.run, TM.step,
    physicalStackV2Tape, Tape.write,
    Tape.move, PhysicalStackRepV2, List.map_cons, List.replicate_succ,
    Nat.add_comm]
  exact ⟨padding + 1, by
    simp [physicalStackV2Tape, List.replicate_succ, Nat.add_comm]⟩

#print axioms MCore.Real.P01FullVerifierStackPrimitiveMachine.push_run_one
#print axioms MCore.Real.P01FullVerifierStackPrimitiveMachine.push_run_one_rep
#print axioms MCore.Real.P01FullVerifierStackPrimitiveMachine.pop_run_two_false
#print axioms MCore.Real.P01FullVerifierStackPrimitiveMachine.pop_run_two_true

end P01FullVerifierStackPrimitiveMachine
end Real
end MCore
