import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01FinalSourceEmptyCheck

open CanonicalFinalProof
open P01EvalCursorMachine
open P01NTMRunLaws

/-- Final verifier guard.

The evaluator finishes at the physical stack-end blank.  With an empty frame
stack, one blank immediately to the left is the stack/source separator.  The
next cell is:
* blank iff the unread source tail is empty;
* a bit iff some source remains unconsumed.

The semantic Boolean is carried in finite control while this fixed check runs. -/
inductive FinalSourceCheckState where
  | start : Bool → FinalSourceCheckState
  | separator : Bool → FinalSourceCheckState
  | inspect : Bool → FinalSourceCheckState
  | accept : Bool → FinalSourceCheckState
  | reject
  deriving DecidableEq, Repr

def finalSourceCheckMachine :
    NTM FinalSourceCheckState (Option Bool) where
  initial := .start false
  blank := none
  transition := fun q symbol =>
    match q with
    | .start v =>
        match symbol with
        | none => [(.separator v, none, .left)]
        | some b => [(.reject, some b, .stay)]
    | .separator v =>
        match symbol with
        | none => [(.inspect v, none, .left)]
        | some b => [(.reject, some b, .stay)]
    | .inspect v =>
        match symbol with
        | none => [(.accept v, none, .stay)]
        | some b => [(.reject, some b, .stay)]
    | .accept _ => []
    | .reject => []
  accepting := fun q =>
    match q with
    | .accept true => true
    | _ => false
  rejecting := fun q =>
    match q with
    | .accept false => true
    | .reject => true
    | _ => false

abbrev FinalCheckConfig :=
  Configuration FinalSourceCheckState (Option Bool)

def finalCheckStart
    (v : Bool)
    (witness unread : BitString)
    (consumed padding : Nat) :
    FinalCheckConfig :=
  { state := .start v,
    tape :=
      evalCursorStackEndTape witness consumed unread [] padding }

@[simp] theorem finalSourceCheckMachine_blank :
    finalSourceCheckMachine.blank = none := rfl

@[simp] theorem accept_true_accepting :
    finalSourceCheckMachine.accepting (.accept true) = true := rfl

@[simp] theorem accept_false_rejecting :
    finalSourceCheckMachine.rejecting (.accept false) = true := rfl

@[simp] theorem reject_rejecting :
    finalSourceCheckMachine.rejecting .reject = true := rfl

/-- Empty unread source: after three fixed physical steps the guard preserves
the semantic value and reaches the corresponding terminal state. -/
theorem empty_source_run
    (v : Bool)
    (witness : BitString)
    (consumed padding : Nat) :
    ({ state := .accept v,
       tape :=
         Tape.move none .left
           (Tape.move none .left
             (evalCursorStackEndTape witness consumed [] [] padding)) } :
      FinalCheckConfig) ∈
      finalSourceCheckMachine.runBranches 3
        [finalCheckStart v witness [] consumed padding] := by
  cases v <;> cases consumed <;>
    simp [finalCheckStart, finalSourceCheckMachine,
      evalCursorStackEndTape, NTM.runBranches, NTM.successors,
      NTM.stepBranch, Halted, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

/-- Nonempty unread source: the second cell past the stack/source separator is
the final unread source bit, so the guard rejects in exactly three steps. -/
theorem nonempty_source_rejects
    (v b : Bool)
    (witness rest : BitString)
    (consumed padding : Nat) :
    ∃ tape : Tape (Option Bool),
      ({ state := .reject, tape := tape } : FinalCheckConfig) ∈
        finalSourceCheckMachine.runBranches 3
          [finalCheckStart v witness (b :: rest) consumed padding] := by
  refine ⟨
    Tape.move none .left
      (Tape.move none .left
        (evalCursorStackEndTape witness consumed (b :: rest) [] padding)),
    ?_⟩
  cases v <;>
    cases hrev : rest.reverse with
    | nil =>
        have hrest : rest = [] := by
          simpa using hrev
        subst rest
        cases b <;>
          simp [finalCheckStart, finalSourceCheckMachine,
            evalCursorStackEndTape, NTM.runBranches, NTM.successors,
            NTM.stepBranch, Halted, Tape.write, Tape.move,
            List.reverse_cons, List.map_append,
            List.replicate_succ, List.append_assoc]
    | cons x xs =>
        cases x <;> cases b <;>
          simp [finalCheckStart, finalSourceCheckMachine,
            evalCursorStackEndTape, NTM.runBranches, NTM.successors,
            NTM.stepBranch, Halted, Tape.write, Tape.move,
            List.reverse_cons, List.map_append, hrev,
            List.replicate_succ, List.append_assoc]

/-- The guard's terminal value agrees with the evaluator Boolean when the
source was fully consumed. -/
theorem empty_source_accepts_iff
    (v : Bool)
    (witness : BitString)
    (consumed padding : Nat) :
    ∃ c ∈ finalSourceCheckMachine.runBranches 3
        [finalCheckStart v witness [] consumed padding],
      (finalSourceCheckMachine.accepting c.state = true ↔ v = true) := by
  let c : FinalCheckConfig :=
    { state := .accept v,
      tape :=
        Tape.move none .left
          (Tape.move none .left
            (evalCursorStackEndTape witness consumed [] [] padding)) }
  refine ⟨c, empty_source_run v witness consumed padding, ?_⟩
  dsimp [c]
  cases v <;> rfl

#print axioms MCore.Real.P01FinalSourceEmptyCheck.empty_source_run
#print axioms MCore.Real.P01FinalSourceEmptyCheck.nonempty_source_rejects
#print axioms MCore.Real.P01FinalSourceEmptyCheck.empty_source_accepts_iff

end P01FinalSourceEmptyCheck
end Real
end MCore
