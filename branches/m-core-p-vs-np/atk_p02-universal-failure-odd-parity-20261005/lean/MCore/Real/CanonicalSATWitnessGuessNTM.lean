import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace CanonicalSATWitnessGuessNTM

open CanonicalFinalProof

/-- Finite-control nondeterministic witness-bit generator.

Protocol: the current finite block determines the witness length.  At each
nonblank cell the machine nondeterministically writes false or true and moves
right.  At the first blank it enters state 1 and halts accepting.

The contents of the input block are irrelevant; only its finite length is used.
This lets a future integrated machine reserve an n-cell work block and generate
all Boolean witnesses of length n without storing n in control. -/
def witnessGuessMachine : NTM (Fin 2) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | none => [(1, none, .stay)]
        | some _ =>
            [(0, some false, .right),
             (0, some true, .right)]
      else
        []
    accepting := fun q => q == 1
    rejecting := fun _ => false }

@[simp] theorem witnessGuessMachine_blank_none :
    witnessGuessMachine.blank = none := rfl

@[simp] theorem witnessGuessMachine_initial :
    witnessGuessMachine.initial = (0 : Fin 2) := rfl

def guessConfig
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

def doneConfig
    (left : List (Option Bool)) :
    Configuration (Fin 2) (Option Bool) :=
  { state := 1
    tape := { left := left, head := none, right := [] } }

@[simp] theorem guessConfig_state
    (left : List (Option Bool))
    (bits : BitString) :
    (guessConfig left bits).state = (0 : Fin 2) := by
  cases bits <;> rfl

@[simp] theorem doneConfig_accepting
    (left : List (Option Bool)) :
    witnessGuessMachine.accepting (doneConfig left).state = true := by
  rfl

theorem witnessGuess_successors_cons
    (left : List (Option Bool))
    (b : Bool)
    (bs : BitString) :
    witnessGuessMachine.successors (guessConfig left (b :: bs)) =
      [ guessConfig (some false :: left) bs,
        guessConfig (some true :: left) bs ] := by
  cases bs <;>
    simp [witnessGuessMachine, guessConfig, NTM.successors,
      NTM.stepBranch, Tape.write, Tape.move]

theorem witnessGuess_successors_nil
    (left : List (Option Bool)) :
    witnessGuessMachine.successors (guessConfig left []) =
      [doneConfig left] := by
  simp [witnessGuessMachine, guessConfig, doneConfig, NTM.successors,
    NTM.stepBranch, Tape.write, Tape.move]

def witnessGuessTimeBound : TimeBound :=
  fun n => n + 1

theorem witnessGuessTimeBound_poly :
    PolynomialTimeBound witnessGuessTimeBound := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp [witnessGuessTimeBound]

/-- Type-level firewall: the guesser has fixed finite control and the canonical
fixed tape alphabet. -/
theorem witnessGuessMachine_canonical_type :
    Nonempty (NTM (Fin 2) (Option Bool)) :=
  ⟨witnessGuessMachine⟩

#print axioms MCore.Real.CanonicalSATWitnessGuessNTM.witnessGuess_successors_cons
#print axioms MCore.Real.CanonicalSATWitnessGuessNTM.witnessGuess_successors_nil
#print axioms MCore.Real.CanonicalSATWitnessGuessNTM.witnessGuessTimeBound_poly
#print axioms MCore.Real.CanonicalSATWitnessGuessNTM.witnessGuessMachine_canonical_type

end CanonicalSATWitnessGuessNTM
end Real
end MCore
