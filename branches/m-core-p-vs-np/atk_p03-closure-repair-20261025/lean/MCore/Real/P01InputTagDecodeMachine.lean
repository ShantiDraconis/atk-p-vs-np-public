import MCore.Real.P01EvalCursorMachine

namespace MCore
namespace Real
namespace P01InputTagDecodeMachine

open CanonicalFinalProof
open P01EvalCursorMachine

/-- Fixed finite-control decoder for the three-bit expression tag.

The three tag bits are stored only in control, erased from the source region,
and the head advances to the first bit after the tag. -/
inductive TagDecodeState where
  | start
  | got0 (b0 : Bool)
  | got1 (b0 b1 : Bool)
  | halt (b0 b1 b2 : Bool)
  | reject
  deriving DecidableEq, Repr

def tagDecodeMachine : TM TagDecodeState (Option Bool) where
  initial := .start
  blank := none
  transition := fun q symbol =>
    match q with
    | .start =>
        match symbol with
        | some b0 => (.got0 b0, none, .right)
        | none => (.reject, none, .stay)
    | .got0 b0 =>
        match symbol with
        | some b1 => (.got1 b0 b1, none, .right)
        | none => (.reject, none, .stay)
    | .got1 b0 b1 =>
        match symbol with
        | some b2 => (.halt b0 b1 b2, none, .right)
        | none => (.reject, none, .stay)
    | .halt b0 b1 b2 => (.halt b0 b1 b2, symbol, .stay)
    | .reject => (.reject, symbol, .stay)
  halting := fun q =>
    match q with
    | .halt _ _ _ => true
    | .reject => true
    | _ => false

@[simp] theorem tagDecodeMachine_blank :
    tagDecodeMachine.blank = none := rfl

@[simp] theorem tagDecodeMachine_halt
    (b0 b1 b2 : Bool) :
    tagDecodeMachine.halting (.halt b0 b1 b2) = true := rfl

/-- Exact three-step physical tag decode on the evaluator cursor layout. -/
theorem tagDecode_run_three
    (witness tail frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool) :
    tagDecodeMachine.run 3
      { state := tagDecodeMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (b0 :: b1 :: b2 :: tail) frameStack padding } =
      { state := .halt b0 b1 b2,
        tape :=
          evalCursorReadTape witness (consumed + 3)
            tail frameStack padding } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases tail <;> cases consumed <;>
    simp [tagDecodeMachine, evalCursorReadTape,
      TM.run, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

/-- The decoder halts within the same fixed three-step budget. -/
theorem tagDecode_halts
    (witness tail frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool) :
    tagDecodeMachine.HaltsWithin 3
      { state := tagDecodeMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (b0 :: b1 :: b2 :: tail) frameStack padding } := by
  unfold TM.HaltsWithin
  rw [tagDecode_run_three]
  exact tagDecodeMachine_halt b0 b1 b2

#print axioms MCore.Real.P01InputTagDecodeMachine.tagDecode_run_three
#print axioms MCore.Real.P01InputTagDecodeMachine.tagDecode_halts

end P01InputTagDecodeMachine
end Real
end MCore
