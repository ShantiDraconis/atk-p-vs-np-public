import MCore.Real.CanonicalSATFrameAttack

namespace MCore
namespace Real
namespace CanonicalSATFrameMachineV2

open CanonicalFinalProof
open CanonicalSATFrameAttack

/-- Infinite-blank tape semantics: explicit blank cells to the left of the
current head are observationally irrelevant. This is the left-hand analogue
of `readTapeCells` ignoring trailing blanks on the right. -/
def LeftBlankPadding (t : Tape (Option Bool)) : Prop :=
  ∀ s ∈ t.left, s = none

def TapeRepresentsModuloBlankPadding
    (bits : BitString) (t : Tape (Option Bool)) : Prop :=
  LeftBlankPadding t ∧ tapeWord t = bits

def paddedInputTape (k : Nat) : BitString → Tape (Option Bool)
  | [] =>
      { left := List.replicate k none
        head := none
        right := [] }
  | b :: bs =>
      { left := List.replicate k none
        head := some b
        right := bs.map some }

theorem paddedInputTape_represents
    (k : Nat) (bits : BitString) :
    TapeRepresentsModuloBlankPadding bits (paddedInputTape k bits) := by
  cases bits <;>
    simp [TapeRepresentsModuloBlankPadding, LeftBlankPadding,
      paddedInputTape, tapeWord, readTapeCells]

/-- Five-state finite-control machine implementing the frame command protocol.
State 0 dispatches on the command bit. A push command erases one prefix cell
and halts. A pop command erases the command plus the three fixed-width frame
bits and halts at the first stack bit. -/
def frameCommandMachine : TM (Fin 5) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some true => (4, none, .right)
        | some false => (1, none, .right)
        | none => (4, none, .stay)
      else if q = 1 then
        (2, none, .right)
      else if q = 2 then
        (3, none, .right)
      else if q = 3 then
        (4, none, .right)
      else
        (4, symbol, .stay)
    halting := fun q => q == 4 }

@[simp] theorem frameCommandMachine_halt4 :
    frameCommandMachine.halting (4 : Fin 5) = true := by rfl

@[simp] theorem frameCommandMachine_not_halt0 :
    frameCommandMachine.halting (0 : Fin 5) = false := by rfl

/-- Push is one semantic machine step; extra fuel is inert after the halting
state is reached. -/
theorem frameCommandMachine_run_push
    (f : Frame) (fs : List Frame) :
    frameCommandMachine.run 4
      (initialTMConfig frameCommandMachine (pushCommand f fs)) =
      { state := (4 : Fin 5)
        tape := paddedInputTape 1 (encodeFrames (f :: fs)) } := by
  cases f <;>
    simp [frameCommandMachine, TM.run, TM.step, initialTMConfig,
      pushCommand, encodeFrames, encodeFrame, inputTape,
      paddedInputTape, Tape.write, Tape.move]

/-- Pop erases exactly four protocol cells: command + one three-bit frame. -/
theorem frameCommandMachine_run_pop
    (f : Frame) (fs : List Frame) :
    frameCommandMachine.run 4
      (initialTMConfig frameCommandMachine (popCommand (f :: fs))) =
      { state := (4 : Fin 5)
        tape := paddedInputTape 4 (encodeFrames fs) } := by
  cases f <;>
  cases fs with
  | nil =>
      simp [frameCommandMachine, TM.run, TM.step, initialTMConfig,
        popCommand, encodeFrames, encodeFrame, inputTape,
        paddedInputTape, Tape.write, Tape.move]
  | cons g gs =>
      cases g <;>
        simp [frameCommandMachine, TM.run, TM.step, initialTMConfig,
          popCommand, encodeFrames, encodeFrame, inputTape,
          paddedInputTape, Tape.write, Tape.move]

def frameCommandTimeBound : TimeBound := fun _ => 4

theorem frameCommandTimeBound_poly :
    PolynomialTimeBound frameCommandTimeBound := by
  refine ⟨4, 0, ?_⟩
  intro n
  simp [frameCommandTimeBound]

structure BlankNormalizedFrameTapeMachineCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  push_halts :
    ∀ (f : Frame) (fs : List Frame),
      machine.HaltsWithin
        (timeBound (pushCommand f fs).length)
        (initialTMConfig machine (pushCommand f fs))
  push_correct :
    ∀ (f : Frame) (fs : List Frame),
      TapeRepresentsModuloBlankPadding
        (encodeFrames (f :: fs))
        (machine.run
          (timeBound (pushCommand f fs).length)
          (initialTMConfig machine (pushCommand f fs))).tape
  pop_halts :
    ∀ (f : Frame) (fs : List Frame),
      machine.HaltsWithin
        (timeBound (popCommand (f :: fs)).length)
        (initialTMConfig machine (popCommand (f :: fs)))
  pop_correct :
    ∀ (f : Frame) (fs : List Frame),
      TapeRepresentsModuloBlankPadding
        (encodeFrames fs)
        (machine.run
          (timeBound (popCommand (f :: fs)).length)
          (initialTMConfig machine (popCommand (f :: fs)))).tape

def frameCommandMachine_certificate :
    BlankNormalizedFrameTapeMachineCertificate := by
  refine
    { stateCount := 4
      machine := frameCommandMachine
      blank_none := rfl
      timeBound := frameCommandTimeBound
      time_poly := frameCommandTimeBound_poly
      push_halts := ?_
      push_correct := ?_
      pop_halts := ?_
      pop_correct := ?_ }
  · intro f fs
    rw [TM.HaltsWithin]
    simp [frameCommandTimeBound, frameCommandMachine_run_push]
  · intro f fs
    rw [frameCommandTimeBound, frameCommandMachine_run_push]
    exact paddedInputTape_represents 1 _
  · intro f fs
    rw [TM.HaltsWithin]
    simp [frameCommandTimeBound, frameCommandMachine_run_pop]
  · intro f fs
    rw [frameCommandTimeBound, frameCommandMachine_run_pop]
    exact paddedInputTape_represents 4 _

def BlankNormalizedFrameTapeOperationalGap : Prop :=
  Nonempty BlankNormalizedFrameTapeMachineCertificate

theorem blank_normalized_frame_tape_operational_closed :
    BlankNormalizedFrameTapeOperationalGap :=
  ⟨frameCommandMachine_certificate⟩

#print axioms MCore.Real.CanonicalSATFrameMachineV2.frameCommandMachine_run_push
#print axioms MCore.Real.CanonicalSATFrameMachineV2.frameCommandMachine_run_pop
#print axioms MCore.Real.CanonicalSATFrameMachineV2.frameCommandTimeBound_poly
#print axioms MCore.Real.CanonicalSATFrameMachineV2.frameCommandMachine_certificate
#print axioms MCore.Real.CanonicalSATFrameMachineV2.blank_normalized_frame_tape_operational_closed

end CanonicalSATFrameMachineV2
end Real
end MCore
