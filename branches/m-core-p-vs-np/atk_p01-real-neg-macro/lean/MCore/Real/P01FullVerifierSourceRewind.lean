import MCore.Real.P01FullVerifierPhysicalShuttles

namespace MCore
namespace Real
namespace P01FullVerifierSourceRewind

open CanonicalFinalProof
open P01FullVerifierPhysicalShuttles

/-- Three-state local macro:
0 enters the source from the source-end blank;
1 scans left across source bits until the witness/source separator blank;
2 halts after moving right to the first source cell (or source-end blank if empty).
-/
abbrev RewindState := Fin 3

def enterSource : RewindState := 0
def scanLeft : RewindState := 1
def rewindHalt : RewindState := 2

def sourceRewindMachine : TM RewindState (Option Bool) :=
  { initial := enterSource
    blank := none
    transition := fun q symbol =>
      if q = enterSource then
        (scanLeft, symbol, .left)
      else if q = scanLeft then
        match symbol with
        | some b => (scanLeft, some b, .left)
        | none => (rewindHalt, none, .right)
      else
        (rewindHalt, symbol, .stay)
    halting := fun q => q == rewindHalt }

@[simp] theorem sourceRewindMachine_blank :
    sourceRewindMachine.blank = none := rfl

@[simp] theorem enterSource_not_halted :
    sourceRewindMachine.halting enterSource = false := by decide

@[simp] theorem scanLeft_not_halted :
    sourceRewindMachine.halting scanLeft = false := by decide

@[simp] theorem rewindHalt_halted :
    sourceRewindMachine.halting rewindHalt = true := by decide

def sourceRewindTimeBound : TimeBound :=
  fun n => n + 2

theorem sourceRewindTimeBound_poly :
    PolynomialTimeBound sourceRewindTimeBound := by
  refine ⟨2, 1, ?_⟩
  intro n
  simp [sourceRewindTimeBound]
  omega

/-- First physical step from source-end enters the last source cell, or the
separator itself when the source is empty. -/
theorem sourceRewind_enter_step
    (witness source : BitString) :
    sourceRewindMachine.step
      { state := enterSource, tape := sourceEndTape witness source } =
      { state := scanLeft,
        tape := Tape.move none .left (sourceEndTape witness source) } := by
  simp [sourceRewindMachine, enterSource, scanLeft, TM.step, Tape.write]

/-- Once the separator blank is under the head, one legal right move reaches
the source-start side and enters the halting state. -/
theorem sourceRewind_separator_step
    (t : Tape (Option Bool))
    (hhead : t.head = none) :
    sourceRewindMachine.step { state := scanLeft, tape := t } =
      { state := rewindHalt, tape := Tape.move none .right t } := by
  cases t with
  | mk left head right =>
      cases head with
      | none =>
          simp [sourceRewindMachine, scanLeft, rewindHalt, enterSource,
            TM.step, Tape.write]
      | some b =>
          simp at hhead

#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewindTimeBound_poly
#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_enter_step
#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_separator_step

end P01FullVerifierSourceRewind
end Real
end MCore
