import MCore.Real.P01EvalCursorMachine

namespace MCore
namespace Real
namespace P01NeedExprTagDecode

open CanonicalFinalProof
open P01EvalCursorMachine

/-- The six valid evaluator prefix tags plus the two invalid 3-bit patterns. -/
inductive NeedExprTag where
  | input
  | constFalse
  | constTrue
  | neg
  | and
  | or
  | invalid110
  | invalid111
  deriving DecidableEq, Repr

def decodeTagBits (b0 b1 b2 : Bool) : NeedExprTag :=
  match b0, b1, b2 with
  | false, false, false => .input
  | false, false, true  => .constFalse
  | false, true, false  => .constTrue
  | false, true, true   => .neg
  | true, false, false  => .and
  | true, false, true   => .or
  | true, true, false   => .invalid110
  | true, true, true    => .invalid111

inductive TagDecodeState where
  | start
  | bit1 (b0 : Bool)
  | bit2 (b0 b1 : Bool)
  | halt (tag : NeedExprTag)
  | reject
  deriving DecidableEq, Repr

/-- Fixed finite-control 3-bit tag decoder.

Starting on the first unread source bit, it erases exactly three tag cells,
stores the decoded tag in finite control, and stops on the first source cell
after the tag.  The witness, frame stack, and padding are untouched. -/
def tagDecodeMachine : TM TagDecodeState (Option Bool) where
  initial := .start
  blank := none
  transition := fun q symbol =>
    match q with
    | .start =>
        match symbol with
        | some b0 => (.bit1 b0, none, .right)
        | none => (.reject, none, .stay)
    | .bit1 b0 =>
        match symbol with
        | some b1 => (.bit2 b0 b1, none, .right)
        | none => (.reject, none, .stay)
    | .bit2 b0 b1 =>
        match symbol with
        | some b2 => (.halt (decodeTagBits b0 b1 b2), none, .right)
        | none => (.reject, none, .stay)
    | .halt tag => (.halt tag, symbol, .stay)
    | .reject => (.reject, symbol, .stay)
  halting := fun q =>
    match q with
    | .halt _ => true
    | .reject => true
    | _ => false

@[simp] theorem tagDecodeMachine_halt (tag : NeedExprTag) :
    tagDecodeMachine.halting (.halt tag) = true := rfl

@[simp] theorem tagDecodeMachine_reject :
    tagDecodeMachine.halting .reject = true := rfl

/-- Exact physical 3-bit consumption/decoding theorem. -/
theorem tagDecode_run_three
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool) :
    tagDecodeMachine.run 3
      { state := tagDecodeMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (b0 :: b1 :: b2 :: rest) frameStack padding } =
      { state := .halt (decodeTagBits b0 b1 b2),
        tape :=
          evalCursorReadTape witness (consumed + 3)
            rest frameStack padding } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases rest <;>
    simp [tagDecodeMachine, decodeTagBits, evalCursorReadTape,
      TM.run, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

/-- The decoder rejects if fewer than three source bits remain. -/
theorem tagDecode_rejects_short
    (witness frameStack : BitString)
    (consumed padding : Nat) :
    (tagDecodeMachine.run 1
      { state := tagDecodeMachine.initial,
        tape := evalCursorReadTape witness consumed [] frameStack padding }).state =
      .reject := by
  simp [tagDecodeMachine, evalCursorReadTape, TM.run, TM.step,
    Tape.write, Tape.move]


/-- Any source shorter than one complete three-bit tag is rejected by the
physical decoder within the fixed three-step envelope. -/
theorem tagDecode_rejects_short_three
    (witness bits frameStack : BitString)
    (consumed padding : Nat)
    (hshort : bits.length < 3) :
    (tagDecodeMachine.run 3
      { state := tagDecodeMachine.initial,
        tape := evalCursorReadTape witness consumed
          bits frameStack padding }).state = .reject := by
  rcases bits with _ | ⟨b0, rest⟩
  · simp [tagDecodeMachine, evalCursorReadTape,
      TM.run, TM.step, Tape.write, Tape.move]
  · rcases rest with _ | ⟨b1, rest⟩
    · cases b0 <;>
        simp [tagDecodeMachine, evalCursorReadTape,
          TM.run, TM.step, Tape.write, Tape.move]
    · rcases rest with _ | ⟨b2, rest⟩
      · cases b0 <;> cases b1 <;>
          simp [tagDecodeMachine, evalCursorReadTape,
            TM.run, TM.step, Tape.write, Tape.move]
      · simp at hshort

#print axioms MCore.Real.P01NeedExprTagDecode.tagDecode_rejects_short_three

#print axioms MCore.Real.P01NeedExprTagDecode.tagDecode_run_three
#print axioms MCore.Real.P01NeedExprTagDecode.tagDecode_rejects_short

end P01NeedExprTagDecode
end Real
end MCore
