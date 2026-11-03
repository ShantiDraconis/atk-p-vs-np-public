import MCore.Real.P02FiniteMachineDescription
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P02MachineSerialization

open CanonicalFinalProof
open CanonicalCircuitBits
open P02FiniteMachineDescription

structure TransitionEntry where
  next : Nat
  write : Option Bool
  move : Direction
  deriving Repr, DecidableEq

structure MachinePayload where
  stateCount : Nat
  initial : Nat
  transitionNone : List TransitionEntry
  transitionFalse : List TransitionEntry
  transitionTrue : List TransitionEntry
  halting : List Bool
  accepting : List Bool
  deriving Repr, DecidableEq

def transitionEntry
    (enc : EncodedMachine)
    (q : Fin (enc.stateCount + 1))
    (s : Option Bool) : TransitionEntry :=
  let t := enc.transition q s
  { next := t.1.val
    write := t.2.1
    move := t.2.2 }

def machinePayload (enc : EncodedMachine) : MachinePayload :=
  { stateCount := enc.stateCount
    initial := enc.initial.val
    transitionNone := List.ofFn (fun q => transitionEntry enc q none)
    transitionFalse := List.ofFn (fun q => transitionEntry enc q (some false))
    transitionTrue := List.ofFn (fun q => transitionEntry enc q (some true))
    halting := List.ofFn enc.halting
    accepting := List.ofFn enc.accepting }

def transitionDefault : TransitionEntry :=
  { next := 0, write := none, move := .stay }

def payloadTransitionList
    (p : MachinePayload) : Option Bool → List TransitionEntry
  | none => p.transitionNone
  | some false => p.transitionFalse
  | some true => p.transitionTrue

def payloadToMachine (p : MachinePayload) : EncodedMachine :=
  let n := p.stateCount
  { stateCount := n
    initial := ⟨p.initial % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    transition := fun q s =>
      let e := (payloadTransitionList p s).getD q.val transitionDefault
      let q' : Fin (n + 1) :=
        ⟨e.next % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
      (q', e.write, e.move)
    halting := fun q => p.halting.getD q.val false
    accepting := fun q => p.accepting.getD q.val false }

theorem list_ofFn_getD
    {n : Nat} {α : Type}
    (f : Fin n → α)
    (i : Fin n)
    (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  rw [List.getD_eq_getElem?_getD]
  simp [List.getElem?_ofFn, i.isLt]

theorem payload_initial_roundtrip
    (enc : EncodedMachine) :
    (payloadToMachine (machinePayload enc)).initial = enc.initial := by
  apply Fin.ext
  simp [payloadToMachine, machinePayload, Nat.mod_eq_of_lt enc.initial.isLt]

theorem payload_halting_roundtrip
    (enc : EncodedMachine)
    (q : Fin (enc.stateCount + 1)) :
    (payloadToMachine (machinePayload enc)).halting q = enc.halting q := by
  change (List.ofFn enc.halting).getD q.val false = enc.halting q
  exact list_ofFn_getD enc.halting q false

theorem payload_accepting_roundtrip
    (enc : EncodedMachine)
    (q : Fin (enc.stateCount + 1)) :
    (payloadToMachine (machinePayload enc)).accepting q = enc.accepting q := by
  change (List.ofFn enc.accepting).getD q.val false = enc.accepting q
  exact list_ofFn_getD enc.accepting q false

theorem payload_transition_roundtrip
    (enc : EncodedMachine)
    (q : Fin (enc.stateCount + 1))
    (s : Option Bool) :
    (payloadToMachine (machinePayload enc)).transition q s =
      enc.transition q s := by
  rcases h : enc.transition q s with ⟨q', w, d⟩
  cases s with
  | none =>
      simp [payloadToMachine, machinePayload, payloadTransitionList,
        transitionEntry, h, list_ofFn_getD, Nat.mod_eq_of_lt q'.isLt]
  | some b =>
      cases b <;>
        simp [payloadToMachine, machinePayload, payloadTransitionList,
          transitionEntry, h, list_ofFn_getD, Nat.mod_eq_of_lt q'.isLt]

theorem payload_toTM_run_roundtrip
    (enc : EncodedMachine)
    (k : Nat)
    (cfg : Configuration (Fin (enc.stateCount + 1)) (Option Bool)) :
    (payloadToMachine (machinePayload enc)).toTM.run k cfg =
      enc.toTM.run k cfg := by
  have hInit := payload_initial_roundtrip enc
  have hTrans : (payloadToMachine (machinePayload enc)).transition = enc.transition := by
    funext q s
    exact payload_transition_roundtrip enc q s
  have hHalt : (payloadToMachine (machinePayload enc)).halting = enc.halting := by
    funext q
    exact payload_halting_roundtrip enc q
  simp only [EncodedMachine.toTM]
  rw [hInit, hTrans, hHalt]

#print axioms MCore.Real.P02MachineSerialization.list_ofFn_getD
#print axioms MCore.Real.P02MachineSerialization.payload_initial_roundtrip
#print axioms MCore.Real.P02MachineSerialization.payload_transition_roundtrip
#print axioms MCore.Real.P02MachineSerialization.payload_halting_roundtrip
#print axioms MCore.Real.P02MachineSerialization.payload_accepting_roundtrip
#print axioms MCore.Real.P02MachineSerialization.payload_toTM_run_roundtrip

end P02MachineSerialization
end Real
end MCore
