import MCore.Real.P01WitnessPreservingPrep
import MCore.Real.CanonicalSATFrameMachineV2
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01FullVerifierTraversal

open CanonicalFinalProof
open P01WitnessPreservingPrep

/-- Fixed two-state scan used by the full verifier to reach the right-hand
blank immediately after the canonical source encoding. -/
def sourceEndScanner : TM (Fin 2) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some b => (0, some b, .right)
        | none => (1, none, .stay)
      else
        (1, symbol, .stay)
    halting := fun q => q == 1 }

@[simp] theorem sourceEndScanner_blank :
    sourceEndScanner.blank = none := rfl

@[simp] theorem sourceEndScanner_halt1 :
    sourceEndScanner.halting (1 : Fin 2) = true := by rfl

@[simp] theorem sourceEndScanner_not_halt0 :
    sourceEndScanner.halting (0 : Fin 2) = false := by rfl

def scanConfig
    (left : List (Option Bool))
    (source : BitString) : Configuration (Fin 2) (Option Bool) :=
  match source with
  | [] =>
      { state := 0, tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := 0,
        tape := { left := left, head := some b, right := bs.map some ++ [none] } }

@[simp] theorem scanConfig_state
    (left : List (Option Bool)) (source : BitString) :
    (scanConfig left source).state = (0 : Fin 2) := by
  cases source <;> rfl

theorem sourceEndScanner_step_cons
    (left : List (Option Bool)) (b : Bool) (bs : BitString) :
    sourceEndScanner.step (scanConfig left (b :: bs)) =
      scanConfig (some b :: left) bs := by
  cases bs <;>
    simp [sourceEndScanner, scanConfig, TM.step, Tape.write, Tape.move]

theorem sourceEndScanner_finish
    (left : List (Option Bool)) :
    sourceEndScanner.run 1 (scanConfig left []) =
      { state := (1 : Fin 2),
        tape := { left := left, head := none, right := [] } } := by
  simp [sourceEndScanner, scanConfig, TM.run, TM.step, Tape.write, Tape.move]

theorem sourceEndScanner_run
    (left : List (Option Bool)) (source : BitString) :
    sourceEndScanner.run (source.length + 1) (scanConfig left source) =
      { state := (1 : Fin 2),
        tape := { left := source.reverse.map some ++ left,
                  head := none, right := [] } } := by
  induction source generalizing left with
  | nil =>
      simpa using sourceEndScanner_finish left
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
      rw [TM.run, scanConfig_state, sourceEndScanner_not_halt0]
      rw [sourceEndScanner_step_cons]
      rw [ih (some b :: left)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem sourceEndScanner_halts
    (left : List (Option Bool)) (source : BitString) :
    sourceEndScanner.HaltsWithin (source.length + 1) (scanConfig left source) := by
  unfold TM.HaltsWithin
  rw [sourceEndScanner_run]
  rfl

/-- For nonempty canonical source, the witness-prep layout is exactly a
scan configuration whose immutable left prefix is blank-delimiter + witness. -/
theorem preparedTape_eq_scanConfig
    (witness : BitString) (b : Bool) (bs : BitString) :
    ({ state := sourceEndScanner.initial,
       tape := preparedTape witness (b :: bs) } : Configuration (Fin 2) (Option Bool)) =
      scanConfig (none :: witness.map some) (b :: bs) := by
  rfl

/-- The fixed scanner therefore reaches the source-end blank from every
nonempty prepared verifier tape in linear time. -/
theorem prepared_source_scan_halts
    (witness : BitString) (b : Bool) (bs : BitString) :
    sourceEndScanner.HaltsWithin ((b :: bs).length + 1)
      { state := sourceEndScanner.initial,
        tape := preparedTape witness (b :: bs) } := by
  rw [preparedTape_eq_scanConfig witness b bs]
  exact sourceEndScanner_halts _ _

def sourceEndScanTimeBound : TimeBound := fun n => n + 1

theorem sourceEndScanTimeBound_poly :
    PolynomialTimeBound sourceEndScanTimeBound := by
  refine ⟨1, 1, ?_⟩
  intro n
  simp [sourceEndScanTimeBound]

/-- Existing certified frame-stack machine is available as the stack
primitive for later bottom-up evaluation. -/
def certifiedFrameStack :=
  CanonicalSATFrameMachineV2.frameCommandMachine_certificate

#print axioms MCore.Real.P01FullVerifierTraversal.sourceEndScanner_run
#print axioms MCore.Real.P01FullVerifierTraversal.prepared_source_scan_halts
#print axioms MCore.Real.P01FullVerifierTraversal.sourceEndScanTimeBound_poly

end P01FullVerifierTraversal
end Real
end MCore
