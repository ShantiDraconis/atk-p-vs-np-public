import MCore.Real.OfficialCookSource

namespace MCore
namespace Real
namespace CookNormalizedMachineModel

open CanonicalFinalProof
open OfficialModel
open OfficialCookSource

/-- Independent normalized deterministic machine syntax for the external-model
lane.  It shares only the generic tape/configuration primitives; it does not
reuse PolyDTMCandidate or TM.run. -/
structure CookDTM where
  stateCount : Nat
  initial : Fin (stateCount + 1)
  transition :
    Fin (stateCount + 1) →
      Option Bool →
      Fin (stateCount + 1) × Option Bool × Direction
  halting : Fin (stateCount + 1) → Bool
  accepting : Fin (stateCount + 1) → Bool

namespace CookDTM

def step
    (M : CookDTM)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool)) :
    Configuration (Fin (M.stateCount + 1)) (Option Bool) :=
  let (nextState, nextSymbol, direction) :=
    M.transition config.state config.tape.head
  { state := nextState
    tape := Tape.move none direction (config.tape.write nextSymbol) }

def run
    (M : CookDTM) :
    Nat →
      Configuration (Fin (M.stateCount + 1)) (Option Bool) →
      Configuration (Fin (M.stateCount + 1)) (Option Bool)
  | 0, config => config
  | fuel + 1, config =>
      if M.halting config.state then config
      else run M fuel (step M config)

def HaltsWithin
    (M : CookDTM)
    (fuel : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool)) : Prop :=
  M.halting (M.run fuel config).state = true

end CookDTM

/-- Independent normalized nondeterministic machine syntax. -/
structure CookNTM where
  stateCount : Nat
  initial : Fin (stateCount + 1)
  transition :
    Fin (stateCount + 1) →
      Option Bool →
      List (Fin (stateCount + 1) × Option Bool × Direction)
  accepting : Fin (stateCount + 1) → Bool
  rejecting : Fin (stateCount + 1) → Bool

namespace CookNTM

def stepBranch
    (M : CookNTM)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (choice : Fin (M.stateCount + 1) × Option Bool × Direction) :
    Configuration (Fin (M.stateCount + 1)) (Option Bool) :=
  let (nextState, nextSymbol, direction) := choice
  { state := nextState
    tape := Tape.move none direction (config.tape.write nextSymbol) }

def successors
    (M : CookNTM)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool)) :
    List (Configuration (Fin (M.stateCount + 1)) (Option Bool)) :=
  (M.transition config.state config.tape.head).map (M.stepBranch config)

def runBranches
    (M : CookNTM) :
    Nat →
      List (Configuration (Fin (M.stateCount + 1)) (Option Bool)) →
      List (Configuration (Fin (M.stateCount + 1)) (Option Bool))
  | 0, configs => configs
  | fuel + 1, configs =>
      let active := configs.filter fun c =>
        !(M.accepting c.state || M.rejecting c.state)
      let halted := configs.filter fun c =>
        M.accepting c.state || M.rejecting c.state
      runBranches M fuel (halted ++ active.flatMap M.successors)

def AcceptsWithin
    (M : CookNTM)
    (fuel : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool)) : Prop :=
  ∃ reached ∈ M.runBranches fuel [config],
    M.accepting reached.state = true

def HaltsWithin
    (M : CookNTM)
    (fuel : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool)) : Prop :=
  ∀ reached ∈ M.runBranches fuel [config],
    M.accepting reached.state = true ∨
      M.rejecting reached.state = true

end CookNTM

def externalInputTape : BitString → Tape (Option Bool)
  | [] =>
      { left := []
        head := none
        right := [] }
  | b :: bs =>
      { left := []
        head := some b
        right := bs.map some }

def initialCookDTMConfig
    (M : CookDTM)
    (x : BitString) :
    Configuration (Fin (M.stateCount + 1)) (Option Bool) :=
  { state := M.initial
    tape := externalInputTape x }

def initialCookNTMConfig
    (M : CookNTM)
    (x : BitString) :
    Configuration (Fin (M.stateCount + 1)) (Option Bool) :=
  { state := M.initial
    tape := externalInputTape x }

structure CookPolyDTMCandidate where
  machine : CookDTM
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def CookPolyDTMCandidate.CorrectAt
    (C : CookPolyDTMCandidate)
    (L : BitLanguage)
    (x : BitString) : Prop :=
  let config := initialCookDTMConfig C.machine x
  C.machine.HaltsWithin (C.timeBound x.length) config ∧
    (C.machine.accepting
        (C.machine.run (C.timeBound x.length) config).state = true
      ↔ L x)

structure CookPolyNTMCandidate where
  machine : CookNTM
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

def CookPolyNTMCandidate.CorrectAt
    (C : CookPolyNTMCandidate)
    (L : BitLanguage)
    (x : BitString) : Prop :=
  let config := initialCookNTMConfig C.machine x
  C.machine.HaltsWithin (C.timeBound x.length) config ∧
    (C.machine.AcceptsWithin (C.timeBound x.length) config ↔ L x)

structure CookPRealization (L : BitLanguage) where
  candidate : CookPolyDTMCandidate
  decides : ∀ x : BitString, candidate.CorrectAt L x

structure CookNPRealization (L : BitLanguage) where
  candidate : CookPolyNTMCandidate
  decides : ∀ x : BitString, candidate.CorrectAt L x

/-- Concrete external formal-model target.  This does not itself assert that
the normalization is definitionally the official problem statement; G3 still
requires the explicit bridge and source-fidelity audit. -/
def cookNormalizedModel : OfficialComplexityModel :=
  { PRealization := CookPRealization
    NPRealization := CookNPRealization }

/-- Bind the concrete formal target to the already-pinned Cook/CMI provenance
record.  Source fidelity and internal/external simulations remain independent
open proof obligations. -/
def cookNormalizedSelection : OfficialModelSelection :=
  { model := cookNormalizedModel
    source := cookCMISource }

theorem cookNormalizedModel_P
    (L : BitLanguage) :
    cookNormalizedModel.P L ↔ Nonempty (CookPRealization L) := by
  rfl

theorem cookNormalizedModel_NP
    (L : BitLanguage) :
    cookNormalizedModel.NP L ↔ Nonempty (CookNPRealization L) := by
  rfl

#print axioms MCore.Real.CookNormalizedMachineModel.cookNormalizedModel_P
#print axioms MCore.Real.CookNormalizedMachineModel.cookNormalizedModel_NP

end CookNormalizedMachineModel
end Real
end MCore
