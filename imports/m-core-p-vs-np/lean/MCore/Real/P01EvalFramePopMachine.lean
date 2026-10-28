import MCore.Real.P01EncodedFrameTape
import MCore.Real.P01FullVerifierPhysicalStackV2

namespace MCore
namespace Real
namespace P01EvalFramePopMachine

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01FullVerifierPhysicalStackV2

/-- Fixed finite-control states for physically reading and removing one
three-bit evaluator frame.  The three bits are accumulated only in finite
control; no unbounded syntax object is stored in the machine state. -/
inductive FramePopState where
  | start
  | read0
  | read1 : Bool → FramePopState
  | read2 : Bool → Bool → FramePopState
  | halt : EvalFrame → FramePopState
  | reject
  deriving DecidableEq, Repr

/-- Decode exactly one three-bit frame in finite control.  Code 111 is rejected
because it is deliberately unused by `encodeEvalFrame`. -/
def decodeBits (b0 b1 b2 : Bool) : Option EvalFrame :=
  decodeEvalFrame [b0, b1, b2]

/-- One fixed physical frame-pop/read machine.

The V2 stack representation keeps a blank cell under the head immediately to
the right of the stack.  We first move left onto bit0, then consume bit0,
bit1, bit2 while erasing them.  The final state carries the decoded finite
frame and the tape again has the canonical blank-head V2 layout. -/
def framePopMachine : TM FramePopState (Option Bool) :=
  { initial := .start
    blank := none
    transition := fun q symbol =>
      match q with
      | .start =>
          match symbol with
          | none => (.read0, none, .left)
          | some b => (.reject, some b, .stay)
      | .read0 =>
          match symbol with
          | none => (.reject, none, .stay)
          | some b0 => (.read1 b0, none, .left)
      | .read1 b0 =>
          match symbol with
          | none => (.reject, none, .stay)
          | some b1 => (.read2 b0 b1, none, .left)
      | .read2 b0 b1 =>
          match symbol with
          | none => (.reject, none, .stay)
          | some b2 =>
              match decodeBits b0 b1 b2 with
              | some f => (.halt f, none, .stay)
              | none => (.reject, none, .stay)
      | .halt f => (.halt f, symbol, .stay)
      | .reject => (.reject, symbol, .stay)
    halting := fun q =>
      match q with
      | .halt _ => true
      | .reject => true
      | _ => false }

@[simp] theorem framePopMachine_blank :
    framePopMachine.blank = none := rfl

def framePopConfig
    (t : Tape (Option Bool)) :
    Configuration FramePopState (Option Bool) :=
  { state := .start, tape := t }

/-- Four physical steps decode and remove exactly one valid evaluator frame.
The remaining stack is unchanged and the three erased cells become blank
padding to the right of the head. -/
theorem framePop_run_four
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrame f ++ stack) padding))
    final.state = .halt f ∧
      final.tape =
        physicalStackV2Tape witness source stack (padding + 3) := by
  cases f with
  | neg =>
      simp [framePopMachine, framePopConfig, decodeBits,
        decodeEvalFrame, encodeEvalFrame, physicalStackV2Tape,
        TM.run, TM.step, Tape.write, Tape.move,
        List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]
  | andLeft =>
      simp [framePopMachine, framePopConfig, decodeBits,
        decodeEvalFrame, encodeEvalFrame, physicalStackV2Tape,
        TM.run, TM.step, Tape.write, Tape.move,
        List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]
  | andRight b =>
      cases b <;>
        simp [framePopMachine, framePopConfig, decodeBits,
          decodeEvalFrame, encodeEvalFrame, physicalStackV2Tape,
          TM.run, TM.step, Tape.write, Tape.move,
          List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc]
  | orLeft =>
      simp [framePopMachine, framePopConfig, decodeBits,
        decodeEvalFrame, encodeEvalFrame, physicalStackV2Tape,
        TM.run, TM.step, Tape.write, Tape.move,
        List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]
  | orRight b =>
      cases b <;>
        simp [framePopMachine, framePopConfig, decodeBits,
          decodeEvalFrame, encodeEvalFrame, physicalStackV2Tape,
          TM.run, TM.step, Tape.write, Tape.move,
          List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc]

/-- Representation-level corollary used by the global evaluator refinement. -/
theorem framePop_run_four_rep
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrame f ++ stack) padding))
    final.state = .halt f ∧
      PhysicalStackRepV2 final.tape witness source stack := by
  dsimp
  have h := framePop_run_four witness source stack padding f
  rcases h with ⟨hs, ht⟩
  exact ⟨hs, ⟨padding + 3, ht⟩⟩

/-- The deliberately unused code 111 is rejected rather than decoded as an
evaluator frame. -/
theorem framePop_rejects_111
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat) :
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (true :: true :: true :: stack) padding))
    final.state = .reject := by
  simp [framePopMachine, framePopConfig, decodeBits,
    decodeEvalFrame, physicalStackV2Tape, TM.run, TM.step,
    Tape.write, Tape.move, List.replicate_succ,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

#print axioms MCore.Real.P01EvalFramePopMachine.framePop_run_four
#print axioms MCore.Real.P01EvalFramePopMachine.framePop_run_four_rep
#print axioms MCore.Real.P01EvalFramePopMachine.framePop_rejects_111

end P01EvalFramePopMachine
end Real
end MCore
