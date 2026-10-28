import MCore.Real.CanonicalSATWitnessGuessNTM

namespace MCore
namespace Real
namespace P01WitnessPreservingPrep

open CanonicalFinalProof

/--
Finite-control witness preprocessor for the canonical single tape.

The machine guesses one witness bit for each input bit while preserving the
input.  It uses the implicit blank immediately to the left of the input as a
delimiter.  During one source-cell cycle the current source bit is temporarily
blanked, a nondeterministic witness bit is appended on the far-left side of
the delimiter, and the source bit is restored before advancing.

State map (Fin 12):
0  START
1  NEXT
2  SOURCE_LEFT_FALSE
3  SOURCE_LEFT_TRUE
4  WITNESS_LEFT_FALSE
5  WITNESS_LEFT_TRUE
6  WITNESS_RIGHT_FALSE
7  WITNESS_RIGHT_TRUE
8  SOURCE_RIGHT_FALSE
9  SOURCE_RIGHT_TRUE
10 FINISH_REWIND
11 HALT
-/
def witnessPreservingPrep : NTM (Fin 12) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some false => [(2, none, .left)]
        | some true  => [(3, none, .left)]
        | none       => [(11, none, .stay)]
      else if q = 1 then
        match symbol with
        | some false => [(2, none, .left)]
        | some true  => [(3, none, .left)]
        | none       => [(10, none, .left)]
      else if q = 2 then
        match symbol with
        | some b => [(2, some b, .left)]
        | none   => [(4, none, .left)]
      else if q = 3 then
        match symbol with
        | some b => [(3, some b, .left)]
        | none   => [(5, none, .left)]
      else if q = 4 then
        match symbol with
        | some b => [(4, some b, .left)]
        | none =>
            [(6, some false, .right),
             (6, some true, .right)]
      else if q = 5 then
        match symbol with
        | some b => [(5, some b, .left)]
        | none =>
            [(7, some false, .right),
             (7, some true, .right)]
      else if q = 6 then
        match symbol with
        | some b => [(6, some b, .right)]
        | none   => [(8, none, .right)]
      else if q = 7 then
        match symbol with
        | some b => [(7, some b, .right)]
        | none   => [(9, none, .right)]
      else if q = 8 then
        match symbol with
        | some b => [(8, some b, .right)]
        | none   => [(1, some false, .right)]
      else if q = 9 then
        match symbol with
        | some b => [(9, some b, .right)]
        | none   => [(1, some true, .right)]
      else if q = 10 then
        match symbol with
        | some b => [(10, some b, .left)]
        | none   => [(11, none, .right)]
      else
        []
    accepting := fun q => q == 11
    rejecting := fun _ => false }

@[simp] theorem witnessPreservingPrep_blank :
    witnessPreservingPrep.blank = none := rfl

@[simp] theorem witnessPreservingPrep_initial :
    witnessPreservingPrep.initial = (0 : Fin 12) := rfl

@[simp] theorem witnessPreservingPrep_accept11 :
    witnessPreservingPrep.accepting (11 : Fin 12) = true := by
  rfl

/-- Conservative cubic budget for the repeated left/right shuttles. -/
def witnessPrepTimeBound : TimeBound :=
  fun n => 64 * (n + 1) ^ 3

theorem witnessPrepTimeBound_poly :
    PolynomialTimeBound witnessPrepTimeBound := by
  exact ⟨64, 3, fun n => Nat.le_refl _⟩

/-- Canonical final layout for a nonempty preserved source:
witness bits live to the left of one blank delimiter and the source head is
restored at its first bit.  One explicit far-right blank is harmless. -/
def preparedTape (witness source : BitString) : Tape (Option Bool) :=
  match source with
  | [] =>
      { left := witness.map some
        head := none
        right := [] }
  | b :: bs =>
      { left := none :: witness.map some
        head := some b
        right := bs.map some ++ [none] }

/-- One-step dispatch stores the current source bit in finite control and
temporarily blanks its cell. -/
theorem start_false_successors
    (bs : BitString) :
    witnessPreservingPrep.successors
        (initialNTMConfig witnessPreservingPrep (false :: bs)) =
      [{ state := (2 : Fin 12)
         tape :=
           Tape.move none .left
             ((inputTape (false :: bs)).write none) }] := by
  simp [witnessPreservingPrep, NTM.successors, NTM.stepBranch,
    initialNTMConfig, inputTape]

theorem start_true_successors
    (bs : BitString) :
    witnessPreservingPrep.successors
        (initialNTMConfig witnessPreservingPrep (true :: bs)) =
      [{ state := (3 : Fin 12)
         tape :=
           Tape.move none .left
             ((inputTape (true :: bs)).write none) }] := by
  simp [witnessPreservingPrep, NTM.successors, NTM.stepBranch,
    initialNTMConfig, inputTape]

/-- Empty input needs no witness cell. -/
theorem empty_successors :
    witnessPreservingPrep.successors
        (initialNTMConfig witnessPreservingPrep []) =
      [{ state := (11 : Fin 12)
         tape := inputTape [] }] := by
  simp [witnessPreservingPrep, NTM.successors, NTM.stepBranch,
    initialNTMConfig, inputTape, Tape.write, Tape.move]

/-- The only branching point writes exactly one Boolean witness symbol. -/
theorem guess_false_state_branches
    (left right : List (Option Bool)) :
    witnessPreservingPrep.successors
      { state := (4 : Fin 12)
        tape := { left := left, head := none, right := right } } =
      [ { state := (6 : Fin 12)
          tape :=
            Tape.move none .right
              { left := left, head := some false, right := right } },
        { state := (6 : Fin 12)
          tape :=
            Tape.move none .right
              { left := left, head := some true, right := right } } ] := by
  simp [witnessPreservingPrep, NTM.successors, NTM.stepBranch,
    Tape.write]

theorem guess_true_state_branches
    (left right : List (Option Bool)) :
    witnessPreservingPrep.successors
      { state := (5 : Fin 12)
        tape := { left := left, head := none, right := right } } =
      [ { state := (7 : Fin 12)
          tape :=
            Tape.move none .right
              { left := left, head := some false, right := right } },
        { state := (7 : Fin 12)
          tape :=
            Tape.move none .right
              { left := left, head := some true, right := right } } ] := by
  simp [witnessPreservingPrep, NTM.successors, NTM.stepBranch,
    Tape.write]

/-- No branch can reject during witness preparation. -/
@[simp] theorem witnessPreservingPrep_never_rejects
    (q : Fin 12) :
    witnessPreservingPrep.rejecting q = false := rfl

#print axioms MCore.Real.P01WitnessPreservingPrep.witnessPrepTimeBound_poly
#print axioms MCore.Real.P01WitnessPreservingPrep.start_false_successors
#print axioms MCore.Real.P01WitnessPreservingPrep.start_true_successors
#print axioms MCore.Real.P01WitnessPreservingPrep.empty_successors
#print axioms MCore.Real.P01WitnessPreservingPrep.guess_false_state_branches
#print axioms MCore.Real.P01WitnessPreservingPrep.guess_true_state_branches

end P01WitnessPreservingPrep
end Real
end MCore
