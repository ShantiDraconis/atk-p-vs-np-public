import MCore.Real.P01EncodedFrameTape
import MCore.Real.P01FullVerifierPhysicalStackV2
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01EvalFramePushMachine

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01FullVerifierPhysicalStackV2
open MachineRunLemmas

/-- Explicit three physical bits of a semantic evaluator frame. -/
def frameBits : EvalFrame → Bool × Bool × Bool
  | .neg            => (false, false, false)
  | .andLeft        => (false, false, true)
  | .andRight false => (false, true, false)
  | .andRight true  => (false, true, true)
  | .orLeft         => (true, false, false)
  | .orRight false  => (true, false, true)
  | .orRight true   => (true, true, false)

def frameBit0 (f : EvalFrame) : Bool := (frameBits f).1
def frameBit1 (f : EvalFrame) : Bool := (frameBits f).2.1
def frameBit2 (f : EvalFrame) : Bool := (frameBits f).2.2

theorem encodeEvalFrame_eq_bits (f : EvalFrame) :
    encodeEvalFrame f = [frameBit0 f, frameBit1 f, frameBit2 f] := by
  cases f with
  | neg => rfl
  | andLeft => rfl
  | andRight b => cases b <;> rfl
  | orLeft => rfl
  | orRight b => cases b <;> rfl

/-- Finite-control states for a three-cell frame push.
The frame value is one of seven finite constructors; it is control data, not
an unbounded circuit/AST. -/
inductive FramePushState where
  | start : EvalFrame → FramePushState
  | after1 : EvalFrame → FramePushState
  | after2 : EvalFrame → FramePushState
  | halt
  | reject
  deriving DecidableEq, Repr

/-- Fixed physical machine: each successful step requires the current cell to
be blank, writes one code bit, and advances right.  Bits are emitted in reverse
temporal order so the left stack prefix ends as bit0::bit1::bit2. -/
def framePushMachine : TM FramePushState (Option Bool) :=
  { initial := .halt
    blank := none
    transition := fun q symbol =>
      match q with
      | .start f =>
          match symbol with
          | none => (.after1 f, some (frameBit2 f), .right)
          | some b => (.reject, some b, .stay)
      | .after1 f =>
          match symbol with
          | none => (.after2 f, some (frameBit1 f), .right)
          | some b => (.reject, some b, .stay)
      | .after2 f =>
          match symbol with
          | none => (.halt, some (frameBit0 f), .right)
          | some b => (.reject, some b, .stay)
      | .halt => (.halt, symbol, .stay)
      | .reject => (.reject, symbol, .stay)
    halting := fun q =>
      match q with
      | .halt => true
      | .reject => true
      | _ => false }

@[simp] theorem framePushMachine_blank :
    framePushMachine.blank = none := rfl

def framePushConfig
    (f : EvalFrame) (t : Tape (Option Bool)) :
    Configuration FramePushState (Option Bool) :=
  { state := .start f, tape := t }

/-- One start-state step is exactly the certified Boolean push transform. -/
theorem framePush_start_one
    (f : EvalFrame) (t : Tape (Option Bool))
    (hblank : t.head = none) :
    framePushMachine.run 1
      { state := FramePushState.start f, tape := t } =
      { state := FramePushState.after1 f,
        tape := pushStep (frameBit2 f) t } := by
  rw [TM.run]
  simp [framePushMachine, hblank, TM.step, pushStep]
  rfl

/-- Second code-bit step. -/
theorem framePush_after1_one
    (f : EvalFrame) (t : Tape (Option Bool))
    (hblank : t.head = none) :
    framePushMachine.run 1
      { state := FramePushState.after1 f, tape := t } =
      { state := FramePushState.after2 f,
        tape := pushStep (frameBit1 f) t } := by
  rw [TM.run]
  simp [framePushMachine, hblank, TM.step, pushStep]
  rfl

/-- Third code-bit step reaches the halting state. -/
theorem framePush_after2_one
    (f : EvalFrame) (t : Tape (Option Bool))
    (hblank : t.head = none) :
    framePushMachine.run 1
      { state := FramePushState.after2 f, tape := t } =
      { state := FramePushState.halt,
        tape := pushStep (frameBit0 f) t } := by
  rw [TM.run]
  simp [framePushMachine, hblank, TM.step, pushStep]
  rfl

/-- Three physical push steps realize exactly the fixed-width frame encoding on
the V2 stack layout.  The proof composes the already-certified Boolean
`pushStep_correct` invariant rather than normalizing raw tape padding. -/
theorem framePush_run_three
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePushMachine.run 3
        (framePushConfig f
          (physicalStackV2Tape witness source stack padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrame f ++ stack)
          (((padding - 1) - 1) - 1) := by
  dsimp
  unfold framePushConfig
  have h1 := framePush_start_one f
    (physicalStackV2Tape witness source stack padding) rfl
  have hp1 := pushStep_correct witness source stack padding (frameBit2 f)
  have h2 := framePush_after1_one f
    (physicalStackV2Tape witness source
      (frameBit2 f :: stack) (padding - 1)) rfl
  have hp2 := pushStep_correct witness source
    (frameBit2 f :: stack) (padding - 1) (frameBit1 f)
  have h3 := framePush_after2_one f
    (physicalStackV2Tape witness source
      (frameBit1 f :: frameBit2 f :: stack) ((padding - 1) - 1)) rfl
  have hp3 := pushStep_correct witness source
    (frameBit1 f :: frameBit2 f :: stack) ((padding - 1) - 1)
    (frameBit0 f)
  rw [show 3 = 1 + 2 by decide, MachineRunLemmas.run_add]
  rw [h1, hp1]
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [h2, hp2]
  rw [h3, hp3]
  constructor
  · rfl
  · rw [encodeEvalFrame_eq_bits]
    rfl

/-- Fail-closed behavior: starting a push on a nonblank cell rejects in one
step instead of overwriting existing data. -/
theorem framePush_rejects_nonblank
    (f : EvalFrame) (b : Bool)
    (left right : List (Option Bool)) :
    (framePushMachine.run 1
      (framePushConfig f
        { left := left, head := some b, right := right })).state =
      .reject := by
  cases f <;> simp [framePushMachine, framePushConfig, TM.run, TM.step]

#print axioms MCore.Real.P01EvalFramePushMachine.framePush_run_three
#print axioms MCore.Real.P01EvalFramePushMachine.framePush_rejects_nonblank

end P01EvalFramePushMachine
end Real
end MCore
