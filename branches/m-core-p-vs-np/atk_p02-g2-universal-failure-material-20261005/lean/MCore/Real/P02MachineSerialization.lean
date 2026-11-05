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
  have hget :
      (payloadTransitionList (machinePayload enc) s).getD q.val transitionDefault =
        transitionEntry enc q s := by
    cases s with
    | none =>
        simpa [payloadTransitionList, machinePayload] using
          (list_ofFn_getD
            (fun i => transitionEntry enc i none) q transitionDefault)
    | some b =>
        cases b with
        | false =>
            simpa [payloadTransitionList, machinePayload] using
              (list_ofFn_getD
                (fun i => transitionEntry enc i (some false)) q transitionDefault)
        | true =>
            simpa [payloadTransitionList, machinePayload] using
              (list_ofFn_getD
                (fun i => transitionEntry enc i (some true)) q transitionDefault)
  have hentry :
      (payloadTransitionList (machinePayload enc) s)[q.val]?.getD transitionDefault =
        transitionEntry enc q s := by
    simpa only [List.getD_eq_getElem?_getD] using hget
  unfold payloadToMachine
  dsimp only
  rcases htrans : enc.transition q s with ⟨q', w, d⟩
  simp [hentry, transitionEntry, htrans]
  apply Fin.ext
  simp [machinePayload, Nat.mod_eq_of_lt q'.isLt]

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


def encodeOptionBool : Option Bool → BitString
  | none => [false, false]
  | some false => [false, true]
  | some true => [true, false]

def decodeOptionBool : BitString → Option (Option Bool × BitString)
  | false :: false :: rest => some (none, rest)
  | false :: true :: rest => some (some false, rest)
  | true :: false :: rest => some (some true, rest)
  | _ => none

@[simp] theorem decodeOptionBool_encode_append
    (s : Option Bool) (tail : BitString) :
    decodeOptionBool (encodeOptionBool s ++ tail) = some (s, tail) := by
  cases s with
  | none => rfl
  | some b => cases b <;> rfl

def encodeDirection : Direction → BitString
  | .left => [false, false]
  | .stay => [false, true]
  | .right => [true, false]

def decodeDirection : BitString → Option (Direction × BitString)
  | false :: false :: rest => some (.left, rest)
  | false :: true :: rest => some (.stay, rest)
  | true :: false :: rest => some (.right, rest)
  | _ => none

@[simp] theorem decodeDirection_encode_append
    (d : Direction) (tail : BitString) :
    decodeDirection (encodeDirection d ++ tail) = some (d, tail) := by
  cases d <;> rfl

def encodeTransitionEntry (e : TransitionEntry) : BitString :=
  encodeNat e.next ++ encodeOptionBool e.write ++ encodeDirection e.move

def decodeTransitionEntry : BitString → Option (TransitionEntry × BitString)
  | bits => do
      let (next, r1) ← decodeNat bits
      let (write, r2) ← decodeOptionBool r1
      let (move, r3) ← decodeDirection r2
      some ({ next := next, write := write, move := move }, r3)

@[simp] theorem decodeTransitionEntry_encode_append
    (e : TransitionEntry) (tail : BitString) :
    decodeTransitionEntry (encodeTransitionEntry e ++ tail) = some (e, tail) := by
  cases e
  simp [encodeTransitionEntry, decodeTransitionEntry, List.append_assoc,
    decodeNat_encodeNat_append]

def encodeRawList {α : Type} (enc : α → BitString) : List α → BitString
  | [] => []
  | x :: xs => enc x ++ encodeRawList enc xs

def decodeN {α : Type}
    (dec : BitString → Option (α × BitString)) :
    Nat → BitString → Option (List α × BitString)
  | 0, bits => some ([], bits)
  | n + 1, bits => do
      let (x, r1) ← dec bits
      let (xs, r2) ← decodeN dec n r1
      some (x :: xs, r2)

theorem decodeN_encodeRawList_append
    {α : Type}
    (enc : α → BitString)
    (dec : BitString → Option (α × BitString))
    (h : ∀ x tail, dec (enc x ++ tail) = some (x, tail)) :
    ∀ xs tail,
      decodeN dec xs.length (encodeRawList enc xs ++ tail) = some (xs, tail) := by
  intro xs
  induction xs with
  | nil =>
      intro tail
      rfl
  | cons x xs ih =>
      intro tail
      simp only [encodeRawList, List.length_cons, decodeN, List.append_assoc]
      rw [h x (encodeRawList enc xs ++ tail)]
      simp [ih tail]

def encodeTransitionList (xs : List TransitionEntry) : BitString :=
  encodeNat xs.length ++ encodeRawList encodeTransitionEntry xs

def decodeTransitionList (bits : BitString) :
    Option (List TransitionEntry × BitString) := do
  let (n, rest) ← decodeNat bits
  decodeN decodeTransitionEntry n rest

@[simp] theorem decodeTransitionList_encode_append
    (xs : List TransitionEntry) (tail : BitString) :
    decodeTransitionList (encodeTransitionList xs ++ tail) = some (xs, tail) := by
  simp [encodeTransitionList, decodeTransitionList, List.append_assoc,
    decodeNat_encodeNat_append,
    decodeN_encodeRawList_append encodeTransitionEntry decodeTransitionEntry
      decodeTransitionEntry_encode_append]

def encodeBoolList (xs : List Bool) : BitString :=
  encodeNat xs.length ++ xs

def decodeBoolList (bits : BitString) : Option (List Bool × BitString) := do
  let (n, rest) ← decodeNat bits
  if h : n ≤ rest.length then
    some (rest.take n, rest.drop n)
  else
    none

@[simp] theorem decodeBoolList_encode_append
    (xs : List Bool) (tail : BitString) :
    decodeBoolList (encodeBoolList xs ++ tail) = some (xs, tail) := by
  simp [encodeBoolList, decodeBoolList, List.append_assoc,
    decodeNat_encodeNat_append]

def encodePayload (p : MachinePayload) : BitString :=
  encodeNat p.stateCount ++
  encodeNat p.initial ++
  encodeTransitionList p.transitionNone ++
  encodeTransitionList p.transitionFalse ++
  encodeTransitionList p.transitionTrue ++
  encodeBoolList p.halting ++
  encodeBoolList p.accepting

def decodePayload (bits : BitString) : Option (MachinePayload × BitString) := do
  let (stateCount, r1) ← decodeNat bits
  let (initial, r2) ← decodeNat r1
  let (transitionNone, r3) ← decodeTransitionList r2
  let (transitionFalse, r4) ← decodeTransitionList r3
  let (transitionTrue, r5) ← decodeTransitionList r4
  let (halting, r6) ← decodeBoolList r5
  let (accepting, r7) ← decodeBoolList r6
  some
    ({ stateCount := stateCount
       initial := initial
       transitionNone := transitionNone
       transitionFalse := transitionFalse
       transitionTrue := transitionTrue
       halting := halting
       accepting := accepting }, r7)

@[simp] theorem decodePayload_encode_append
    (p : MachinePayload) (tail : BitString) :
    decodePayload (encodePayload p ++ tail) = some (p, tail) := by
  cases p
  simp [encodePayload, decodePayload, List.append_assoc,
    decodeNat_encodeNat_append]

def encodeMachine (enc : EncodedMachine) : BitString :=
  encodePayload (machinePayload enc)

def decodeMachine (bits : BitString) : Option EncodedMachine :=
  match decodePayload bits with
  | some (p, []) => some (payloadToMachine p)
  | _ => none

theorem decodeMachine_encodeMachine_target
    (enc : EncodedMachine) :
    decodeMachine (encodeMachine enc) =
      some (payloadToMachine (machinePayload enc)) := by
  have hPayload :
      decodePayload (encodePayload (machinePayload enc)) =
        some (machinePayload enc, []) := by
    simpa using
      (decodePayload_encode_append (machinePayload enc) ([] : BitString))
  simp [decodeMachine, encodeMachine, hPayload]

theorem decoded_accepting_roundtrip
    (enc : EncodedMachine)
    (q : Fin (enc.stateCount + 1)) :
    (payloadToMachine (machinePayload enc)).accepting q =
      enc.accepting q :=
  payload_accepting_roundtrip enc q

theorem decoded_run_roundtrip
    (enc : EncodedMachine)
    (k : Nat)
    (cfg : Configuration (Fin (enc.stateCount + 1)) (Option Bool)) :
    (payloadToMachine (machinePayload enc)).toTM.run k cfg =
      enc.toTM.run k cfg :=
  payload_toTM_run_roundtrip enc k cfg


#print axioms MCore.Real.P02MachineSerialization.list_ofFn_getD
#print axioms MCore.Real.P02MachineSerialization.payload_initial_roundtrip
#print axioms MCore.Real.P02MachineSerialization.payload_transition_roundtrip
#print axioms MCore.Real.P02MachineSerialization.payload_halting_roundtrip
#print axioms MCore.Real.P02MachineSerialization.payload_accepting_roundtrip
#print axioms MCore.Real.P02MachineSerialization.payload_toTM_run_roundtrip
#print axioms MCore.Real.P02MachineSerialization.decodeMachine_encodeMachine_target
#print axioms MCore.Real.P02MachineSerialization.decoded_run_roundtrip

end P02MachineSerialization
end Real
end MCore
