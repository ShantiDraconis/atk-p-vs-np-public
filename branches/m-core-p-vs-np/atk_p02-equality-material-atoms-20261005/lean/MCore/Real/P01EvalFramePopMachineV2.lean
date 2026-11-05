import MCore.Real.P01EvalFramePushMachine

namespace MCore
namespace Real
namespace P01EvalFramePopMachineV2

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalFramePushMachine
open P01FullVerifierPhysicalStackV2
open MachineRunLemmas

/-- Finite-control states for reading and removing one three-bit frame. -/
inductive FramePopState where
  | start
  | read0
  | gap1 : Bool → FramePopState
  | read1 : Bool → FramePopState
  | gap2 : Bool → Bool → FramePopState
  | read2 : Bool → Bool → FramePopState
  | halt : EvalFrame → FramePopState
  | reject
  deriving DecidableEq, Repr

/-- Fixed physical frame-pop machine.
It alternates boundary-to-cell moves and erase/read steps.  The two already-read
bits live in finite control; after the third bit the exact semantic frame is
decoded.  Truncated or malformed input rejects fail-closed. -/
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
          | some b0 => (.gap1 b0, none, .stay)
          | none => (.reject, none, .stay)
      | .gap1 b0 =>
          match symbol with
          | none => (.read1 b0, none, .left)
          | some b => (.reject, some b, .stay)
      | .read1 b0 =>
          match symbol with
          | some b1 => (.gap2 b0 b1, none, .stay)
          | none => (.reject, none, .stay)
      | .gap2 b0 b1 =>
          match symbol with
          | none => (.read2 b0 b1, none, .left)
          | some b => (.reject, some b, .stay)
      | .read2 b0 b1 =>
          match symbol with
          | some b2 =>
              match decodeEvalFrame [b0,b1,b2] with
              | some f => (.halt f, none, .stay)
              | none => (.reject, none, .stay)
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

/-- Writing blank onto an already-blank head is physically inert. -/
theorem tape_write_none_of_head_none
    (t : Tape (Option Bool))
    (h : t.head = none) :
    Tape.write t none = t := by
  cases t with
  | mk left head right =>
      simp [Tape.write] at h ⊢
      exact h.symm

theorem framePop_start_one
    (t : Tape (Option Bool))
    (hblank : t.head = none) :
    framePopMachine.run 1
      { state := FramePopState.start, tape := t } =
      { state := FramePopState.read0, tape := popEnter t } := by
  rw [TM.run]
  simp [framePopMachine, hblank, TM.step, popEnter,
    tape_write_none_of_head_none t hblank, TM.run]

theorem framePop_read0_one
    (b0 : Bool) (t : Tape (Option Bool))
    (hhead : t.head = some b0) :
    framePopMachine.run 1
      { state := FramePopState.read0, tape := t } =
      { state := FramePopState.gap1 b0, tape := popErase t } := by
  rw [TM.run]
  simp [framePopMachine, hhead, TM.step, popErase]
  rfl

theorem framePop_gap1_one
    (b0 : Bool) (t : Tape (Option Bool))
    (hblank : t.head = none) :
    framePopMachine.run 1
      { state := FramePopState.gap1 b0, tape := t } =
      { state := FramePopState.read1 b0, tape := popEnter t } := by
  rw [TM.run]
  simp [framePopMachine, hblank, TM.step, popEnter,
    tape_write_none_of_head_none t hblank, TM.run]

theorem framePop_read1_one
    (b0 b1 : Bool) (t : Tape (Option Bool))
    (hhead : t.head = some b1) :
    framePopMachine.run 1
      { state := FramePopState.read1 b0, tape := t } =
      { state := FramePopState.gap2 b0 b1, tape := popErase t } := by
  rw [TM.run]
  simp [framePopMachine, hhead, TM.step, popErase]
  rfl

theorem framePop_gap2_one
    (b0 b1 : Bool) (t : Tape (Option Bool))
    (hblank : t.head = none) :
    framePopMachine.run 1
      { state := FramePopState.gap2 b0 b1, tape := t } =
      { state := FramePopState.read2 b0 b1, tape := popEnter t } := by
  rw [TM.run]
  simp [framePopMachine, hblank, TM.step, popEnter,
    tape_write_none_of_head_none t hblank, TM.run]

theorem framePop_read2_one
    (b0 b1 b2 : Bool) (f : EvalFrame)
    (t : Tape (Option Bool))
    (hhead : t.head = some b2)
    (hdecode : decodeEvalFrame [b0,b1,b2] = some f) :
    framePopMachine.run 1
      { state := FramePopState.read2 b0 b1, tape := t } =
      { state := FramePopState.halt f, tape := popErase t } := by
  rw [TM.run]
  simp [framePopMachine, hhead, hdecode, TM.step, popErase]
  rfl

/-- First physical bit removal. -/
theorem framePop_first_two
    (witness source : BitString)
    (rest : List Bool) (padding : Nat)
    (b0 : Bool) :
    framePopMachine.run 2
      (framePopConfig
        (physicalStackV2Tape witness source (b0 :: rest) padding)) =
      { state := FramePopState.gap1 b0,
        tape := physicalStackV2Tape witness source rest (padding + 1) } := by
  unfold framePopConfig
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [framePop_start_one _ rfl]
  rw [framePop_read0_one b0 _
    (popEnter_head witness source b0 rest padding)]
  rw [popErase_correct]

/-- Second physical bit removal, retaining the first bit in finite control. -/
theorem framePop_second_two
    (witness source : BitString)
    (rest : List Bool) (padding : Nat)
    (b0 b1 : Bool) :
    framePopMachine.run 2
      { state := FramePopState.gap1 b0,
        tape := physicalStackV2Tape witness source (b1 :: rest) padding } =
      { state := FramePopState.gap2 b0 b1,
        tape := physicalStackV2Tape witness source rest (padding + 1) } := by
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [framePop_gap1_one b0 _ rfl]
  rw [framePop_read1_one b0 b1 _
    (popEnter_head witness source b1 rest padding)]
  rw [popErase_correct]

/-- Third bit removal decodes the exact frame and halts. -/
theorem framePop_third_two
    (witness source : BitString)
    (rest : List Bool) (padding : Nat)
    (b0 b1 b2 : Bool) (f : EvalFrame)
    (hdecode : decodeEvalFrame [b0,b1,b2] = some f) :
    framePopMachine.run 2
      { state := FramePopState.gap2 b0 b1,
        tape := physicalStackV2Tape witness source (b2 :: rest) padding } =
      { state := FramePopState.halt f,
        tape := physicalStackV2Tape witness source rest (padding + 1) } := by
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [framePop_gap2_one b0 b1 _ rfl]
  rw [framePop_read2_one b0 b1 b2 f _
    (popEnter_head witness source b2 rest padding) hdecode]
  rw [popErase_correct]

/-- Six physical steps remove exactly one encoded frame and return that exact
frame in the halting control state. -/
theorem framePop_run_six
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat)
    (f : EvalFrame) :
    framePopMachine.run 6
      (framePopConfig
        (physicalStackV2Tape witness source
          (encodeEvalFrame f ++ stack) padding)) =
      { state := FramePopState.halt f,
        tape := physicalStackV2Tape witness source stack (padding + 3) } := by
  rw [encodeEvalFrame_eq_bits]
  simp only [List.cons_append, List.nil_append]
  have hdecode :
      decodeEvalFrame [frameBit0 f, frameBit1 f, frameBit2 f] = some f := by
    rw [← encodeEvalFrame_eq_bits]
    exact decodeEvalFrame_encodeEvalFrame f
  rw [show 6 = 2 + (2 + 2) by decide, MachineRunLemmas.run_add]
  rw [framePop_first_two witness source
    (frameBit1 f :: frameBit2 f :: stack) padding (frameBit0 f)]
  rw [MachineRunLemmas.run_add]
  rw [framePop_second_two witness source
    (frameBit2 f :: stack) (padding + 1) (frameBit0 f) (frameBit1 f)]
  rw [framePop_third_two witness source
    stack (padding + 1 + 1)
    (frameBit0 f) (frameBit1 f) (frameBit2 f) f hdecode]

/-- Empty/truncated stack rejects rather than fabricating a frame. -/
theorem framePop_empty_rejects
    (witness source : BitString) (padding : Nat) :
    (framePopMachine.run 2
      (framePopConfig
        (physicalStackV2Tape witness source [] padding))).state =
      .reject := by
  unfold framePopConfig
  cases padding <;>
    simp [framePopMachine, TM.run, TM.step, physicalStackV2Tape,
      Tape.move, Tape.write]

#print axioms MCore.Real.P01EvalFramePopMachineV2.framePop_run_six
#print axioms MCore.Real.P01EvalFramePopMachineV2.framePop_empty_rejects

end P01EvalFramePopMachineV2
end Real
end MCore
