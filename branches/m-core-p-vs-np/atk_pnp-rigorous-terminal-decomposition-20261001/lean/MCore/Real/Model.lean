import MCore.K5

namespace MCore.Real

inductive Direction where
  | left
  | stay
  | right
  deriving DecidableEq, Repr

structure Tape (Symbol : Type) where
  left : List Symbol
  head : Symbol
  right : List Symbol
  deriving Repr

namespace Tape

def write {Symbol : Type} (t : Tape Symbol) (symbol : Symbol) : Tape Symbol :=
  { t with head := symbol }

def move {Symbol : Type} (blank : Symbol) : Direction → Tape Symbol → Tape Symbol
  | .stay, t => t
  | .left, ⟨[], head, right⟩ =>
      ⟨[], blank, head :: right⟩
  | .left, ⟨next :: rest, head, right⟩ =>
      ⟨rest, next, head :: right⟩
  | .right, ⟨left, head, []⟩ =>
      ⟨head :: left, blank, []⟩
  | .right, ⟨left, head, next :: rest⟩ =>
      ⟨head :: left, next, rest⟩

end Tape

structure Configuration (State Symbol : Type) where
  state : State
  tape : Tape Symbol
  deriving Repr

/-- A deterministic single-tape machine with a total transition function. -/
structure TM (State Symbol : Type) where
  initial : State
  blank : Symbol
  transition : State → Symbol → State × Symbol × Direction
  halting : State → Bool

namespace TM

def step {State Symbol : Type} (machine : TM State Symbol)
    (config : Configuration State Symbol) : Configuration State Symbol :=
  let (nextState, nextSymbol, direction) :=
    machine.transition config.state config.tape.head
  { state := nextState
    tape := Tape.move machine.blank direction (config.tape.write nextSymbol) }

/-- The evaluator is total because fuel decreases structurally.  It does not
    assert that an arbitrary machine halts. -/
def run {State Symbol : Type} (machine : TM State Symbol) :
    Nat → Configuration State Symbol → Configuration State Symbol
  | 0, config => config
  | fuel + 1, config =>
      if machine.halting config.state then config
      else run machine fuel (machine.step config)

def HaltsWithin {State Symbol : Type} (machine : TM State Symbol)
    (fuel : Nat) (config : Configuration State Symbol) : Prop :=
  machine.halting (machine.run fuel config).state = true

def HaltsOn {State Symbol : Type} (machine : TM State Symbol)
    (config : Configuration State Symbol) : Prop :=
  ∃ fuel, machine.HaltsWithin fuel config

end TM

/-- A nondeterministic single-tape machine.  Each configuration has finitely
    many successors, represented by a list. -/
structure NTM (State Symbol : Type) where
  initial : State
  blank : Symbol
  transition : State → Symbol → List (State × Symbol × Direction)
  accepting : State → Bool
  rejecting : State → Bool

namespace NTM

def stepBranch {State Symbol : Type} (machine : NTM State Symbol)
    (config : Configuration State Symbol)
    (choice : State × Symbol × Direction) : Configuration State Symbol :=
  let (nextState, nextSymbol, direction) := choice
  { state := nextState
    tape := Tape.move machine.blank direction (config.tape.write nextSymbol) }

def successors {State Symbol : Type} (machine : NTM State Symbol)
    (config : Configuration State Symbol) : List (Configuration State Symbol) :=
  (machine.transition config.state config.tape.head).map
    (machine.stepBranch config)

/-- All branches reachable in at most the supplied fuel. -/
def runBranches {State Symbol : Type} (machine : NTM State Symbol) :
    Nat → List (Configuration State Symbol) → List (Configuration State Symbol)
  | 0, configs => configs
  | fuel + 1, configs =>
      let active := configs.filter fun c =>
        !(machine.accepting c.state || machine.rejecting c.state)
      let halted := configs.filter fun c =>
        machine.accepting c.state || machine.rejecting c.state
      runBranches machine fuel (halted ++ active.flatMap machine.successors)

def AcceptsWithin {State Symbol : Type} (machine : NTM State Symbol)
    (fuel : Nat) (config : Configuration State Symbol) : Prop :=
  ∃ reached ∈ machine.runBranches fuel [config],
    machine.accepting reached.state = true

def Accepts {State Symbol : Type} (machine : NTM State Symbol)
    (config : Configuration State Symbol) : Prop :=
  ∃ fuel, machine.AcceptsWithin fuel config

def HaltsWithin {State Symbol : Type} (machine : NTM State Symbol)
    (fuel : Nat) (config : Configuration State Symbol) : Prop :=
  ∀ reached ∈ machine.runBranches fuel [config],
    machine.accepting reached.state = true ∨
      machine.rejecting reached.state = true

def HaltsOn {State Symbol : Type} (machine : NTM State Symbol)
    (config : Configuration State Symbol) : Prop :=
  ∃ fuel, machine.HaltsWithin fuel config

end NTM

/-- A runtime bound indexed by encoded input size. -/
abbrev TimeBound := Nat → Nat

end MCore.Real
