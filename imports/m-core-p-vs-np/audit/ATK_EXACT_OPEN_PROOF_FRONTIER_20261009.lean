/-! ATK OPEN MATERIAL FRONTIER — sourced exact Lean bodies; not a kernel-certified final proof. -/


/- BEGIN lean/MCore/Real/P01FullVerifierSourceRewind.lean SHA 30d21ee3d2ba4e65f8a388c2b92635fc179b908f -/
import MCore.Real.P01FullVerifierPhysicalShuttles
import MCore.Real.MachineRunLemmas

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


/-- Exact scan configuration for the unread reversed source. -/
def rewindScanConfig
    (witness : BitString)
    (remaining : BitString)
    (right : List (Option Bool)) :
    Configuration RewindState (Option Bool) :=
  match remaining with
  | [] =>
      { state := scanLeft,
        tape := { left := witness.map some, head := none, right := right } }
  | b :: bs =>
      { state := scanLeft,
        tape := { left := bs.map some ++ none :: witness.map some,
                  head := some b,
                  right := right } }

@[simp] theorem rewindScanConfig_state
    (witness remaining : BitString)
    (right : List (Option Bool)) :
    (rewindScanConfig witness remaining right).state = scanLeft := by
  cases remaining <;> rfl

theorem rewindScan_step_cons
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (right : List (Option Bool)) :
    sourceRewindMachine.step
      (rewindScanConfig witness (b :: bs) right) =
    rewindScanConfig witness bs (some b :: right) := by
  cases bs <;>
    simp [rewindScanConfig, sourceRewindMachine, enterSource, scanLeft,
      rewindHalt, TM.step, Tape.write, Tape.move, List.append_assoc]

theorem rewind_scan_run
    (witness remaining : BitString)
    (right : List (Option Bool)) :
    sourceRewindMachine.run remaining.length
      (rewindScanConfig witness remaining right) =
    rewindScanConfig witness []
      (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons]
      simp only [TM.run, rewindScanConfig_state, scanLeft_not_halted,
        Bool.false_eq_true, if_false]
      rw [rewindScan_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem sourceRewind_enter_to_scan
    (witness source : BitString) :
    sourceRewindMachine.step
      { state := enterSource, tape := sourceEndTape witness source } =
    rewindScanConfig witness source.reverse [none] := by
  cases h : source.reverse with
  | nil =>
      simp [sourceEndTape, rewindScanConfig, sourceRewindMachine,
        enterSource, scanLeft, TM.step, Tape.write, Tape.move, h]
  | cons b bs =>
      simp [sourceEndTape, rewindScanConfig, sourceRewindMachine,
        enterSource, scanLeft, TM.step, Tape.write, Tape.move, h,
        List.append_assoc]

theorem sourceRewind_run_one_enter
    (witness source : BitString) :
    sourceRewindMachine.run 1
      { state := enterSource, tape := sourceEndTape witness source } =
    rewindScanConfig witness source.reverse [none] := by
  rw [TM.run]
  simp only [enterSource_not_halted, Bool.false_eq_true, if_false]
  exact sourceRewind_enter_to_scan witness source

/-- From a canonical source-end tape, the real rewind TM halts within the
linear bound n+2. -/
theorem sourceRewind_halts_linear
    (witness source : BitString) :
    sourceRewindMachine.HaltsWithin
      (source.length + 2)
      { state := enterSource, tape := sourceEndTape witness source } := by
  unfold TM.HaltsWithin
  rw [show source.length + 2 = 1 + (source.length + 1) by omega]
  rw [MachineRunLemmas.run_add]
  rw [sourceRewind_run_one_enter]
  rw [show source.length + 1 = source.reverse.length + 1 by simp]
  rw [MachineRunLemmas.run_add]
  rw [rewind_scan_run]
  simp [rewindScanConfig, sourceRewindMachine, enterSource, scanLeft,
    rewindHalt, TM.run, TM.step, Tape.write, Tape.move]

#print axioms MCore.Real.P01FullVerifierSourceRewind.sourceRewind_halts_linear

end P01FullVerifierSourceRewind
end Real
end MCore

/- END lean/MCore/Real/P01FullVerifierSourceRewind.lean -/

/- BEGIN imports/pnp/b406b806/lean/MCore/Real/FinalExternalTwoGap.lean SHA e69542b077ccd7b375c47fbc14a72fd03e9bf2ac -/
import MCore.Real.P01FinalCertificate
import MCore.Real.P02G21G22Attack
import MCore.Real.CookNormalizedG3Contract
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace FinalExternalTwoGap

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open CanonicalSATNTMAttack
open P01FinalCertificate
open P02TerminalFrontier
open P02G21G22Attack
open CookNormalizedG3Contract
open FinalExternalCertificate
open FailProofAllGaps
open OfficialModel

/-- The final external lane has exactly two remaining mathematical producers:
P01 HARD and the pointwise G2.1 lower-bound producer. G3 is supplied by the
already-certified normalized external contract. -/
def FinalExternalTwoGap : Prop :=
  P01ConstructionGap ∧ G21Pointwise

/-- The two terminal producers imply the repository's exact FinalExternalGap.
This theorem remains in Prop, so no computational witness is extracted from
Nonempty merely for packaging. -/
theorem final_external_gap_of_two_gap
    (h : FinalExternalTwoGap) :
    FinalExternalGap := by
  rcases h with ⟨hP01, hG21⟩
  have hG1 : SATInNPGap circuitBitEncoding := by
    exact construction_closes_p01 hP01
  have hP02 : P02Target :=
    g21_pointwise_iff_p02_target.mp hG21
  rcases hP02 with ⟨G⟩
  exact
    ⟨{ g1 := hG1
       g2 := G
       g3 := cookNormalizedExternalContract }⟩

/-- Once the two terminal producers are closed, the existing external
certificate pipeline closes with no additional mathematical producer. -/
theorem final_external_two_gap_closes
    (h : FinalExternalTwoGap) :
    ∃ S : OfficialModelSelection,
      OfficialPneqNP S.model.P S.model.NP := by
  exact final_external_gap_closes
    (final_external_gap_of_two_gap h)

#print axioms MCore.Real.FinalExternalTwoGap.final_external_gap_of_two_gap
#print axioms MCore.Real.FinalExternalTwoGap.final_external_two_gap_closes

end FinalExternalTwoGap
end Real
end MCore

/- END imports/pnp/b406b806/lean/MCore/Real/FinalExternalTwoGap.lean -/

/- BEGIN imports/pnp/c102d9d4/lean/MCore/Real/P02G21G22Attack.lean SHA ffd00b23cbbf4cb09f1f8c2ded111c32dbf62571 -/
import MCore.Real.P02TerminalFrontier

namespace MCore
namespace Real
namespace P02G21G22Attack

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open FailProofAllGaps
open P02TerminalFrontier

/-- The fixed canonical SAT bit-language used by the P02 frontier. -/
abbrev SATTarget : BitLanguage :=
  SATBits circuitBitEncoding

/-- G2.1 in its minimal pointwise form: every deterministic polynomial-time
candidate has a concrete input on which it fails for the canonical SAT target.
This is the exact OPEN_MATH producer; no stronger diagonalization syntax is
silently assumed here. -/
def G21Pointwise : Prop :=
  ∀ candidate : PolyDTMCandidate,
    ∃ x : BitString,
      ¬ candidate.CorrectAt SATTarget x

/-- G2.2 is the contradiction consumer: no purported total P-realization of
the canonical SAT target can coexist with G2.1. -/
def G22Contradiction : Prop :=
  ∀ realization : PolyDTMRealization SATTarget, False

/-- The pointwise G2.1 statement is exactly the already-pinned P02 target. -/
theorem g21_pointwise_iff_p02_target :
    G21Pointwise ↔ P02Target := by
  simpa [G21Pointwise, P02Target, SATTarget, SATFailGap] using
    (failure_generator_iff_universal_failure
      (language := SATBits circuitBitEncoding)).symm

/-- G2.2 is exactly non-membership of the canonical SAT target in the
hardened deterministic class. -/
theorem g22_contradiction_iff_not_in_p :
    G22Contradiction ↔ ¬ InP SATTarget := by
  constructor
  · intro h hP
    rcases hP with ⟨realization⟩
    exact h realization
  · intro h realization
    exact h ⟨realization⟩

/-- Once G2.1 is supplied, G2.2 closes with no additional mathematical
assumption. -/
theorem g21_implies_g22
    (hG21 : G21Pointwise) :
    G22Contradiction := by
  apply g22_contradiction_iff_not_in_p.mpr
  exact p02_target_iff_sat_not_in_p.mp
    (g21_pointwise_iff_p02_target.mp hG21)

/-- Conversely, a completed G2.2 contradiction already contains the exact
G2.1 lower-bound content. Thus G2.2 is not an independent terminal producer. -/
theorem g22_implies_g21
    (hG22 : G22Contradiction) :
    G21Pointwise := by
  apply g21_pointwise_iff_p02_target.mpr
  apply p02_target_iff_sat_not_in_p.mpr
  exact g22_contradiction_iff_not_in_p.mp hG22

theorem g21_iff_g22 :
    G21Pointwise ↔ G22Contradiction :=
  ⟨g21_implies_g22, g22_implies_g21⟩

/-- P01 plus the exact G2.1 producer closes the internal separation. -/
theorem p01_g21_closes_internal
    (hP01 : SATInNPGap circuitBitEncoding)
    (hG21 : G21Pointwise) :
    PneqNP := by
  exact p01_p02_close_internal_separation
    hP01
    (g21_pointwise_iff_p02_target.mp hG21)

#print axioms MCore.Real.P02G21G22Attack.g21_pointwise_iff_p02_target
#print axioms MCore.Real.P02G21G22Attack.g22_contradiction_iff_not_in_p
#print axioms MCore.Real.P02G21G22Attack.g21_implies_g22
#print axioms MCore.Real.P02G21G22Attack.g22_implies_g21
#print axioms MCore.Real.P02G21G22Attack.g21_iff_g22
#print axioms MCore.Real.P02G21G22Attack.p01_g21_closes_internal

end P02G21G22Attack
end Real
end MCore

/- END imports/pnp/c102d9d4/lean/MCore/Real/P02G21G22Attack.lean -/

/- BEGIN imports/pnp/c102d9d4/lean/MCore/Real/FinalExternalCertificate.lean SHA 12c9dbd5fd2fca8e2c1634d6cc5cec87fdefe1a3 -/
import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits
import MCore.Real.G3ModelMatch

namespace MCore
namespace Real
namespace FinalExternalCertificate

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open FailProofAllGaps
open OfficialModel
open G3ModelMatch

/-- Exact three-producer payload for external promotion.

G1: concrete canonical SAT NP realization.
G2: concrete universal deterministic failure generator.
G3: explicit external-model selection, provenance, normalization and two-way
polynomial simulations. -/
structure FinalExternalInputs where
  g1 : SATInNPGap circuitBitEncoding
  g2 : FailureGenerator (SATBits circuitBitEncoding)
  g3 : G3ExternalContract

def FinalExternalInputs.toSATExternalClosure
    (I : FinalExternalInputs) :
    SATExternalClosure I.g3.selection.model.P I.g3.selection.model.NP :=
  { encoding := circuitBitEncoding
    sat_in_np := I.g1
    fail_generator := I.g2
    model_match := I.g3.toExternalModelMatch }

def FinalExternalInputs.toFinalGapCertificate
    (I : FinalExternalInputs) :
    FinalGapCertificate I.g3.selection.model.P I.g3.selection.model.NP :=
  { target := SATBits circuitBitEncoding
    target_in_np := I.g1
    fail_generator := I.g2
    model_match := I.g3.toExternalModelMatch }

theorem final_external_certificate
    (I : FinalExternalInputs) :
    OfficialPneqNP I.g3.selection.model.P I.g3.selection.model.NP := by
  exact final_gap_certificate_closes I.toFinalGapCertificate

def FinalExternalGap : Prop :=
  Nonempty FinalExternalInputs

theorem final_external_gap_closes
    (h : FinalExternalGap) :
    ∃ S : OfficialModelSelection,
      OfficialPneqNP S.model.P S.model.NP := by
  rcases h with ⟨I⟩
  exact ⟨I.g3.selection, final_external_certificate I⟩

#print axioms MCore.Real.FinalExternalCertificate.final_external_certificate
#print axioms MCore.Real.FinalExternalCertificate.final_external_gap_closes

end FinalExternalCertificate
end Real
end MCore

/- END imports/pnp/c102d9d4/lean/MCore/Real/FinalExternalCertificate.lean -/

/-! EXACT OPEN OBLIGATIONS (not assumed as axioms):
P01: Nonempty P01MachineConstruction; fixed NTM, blank_none, polynomial bound, all-input halting, acceptance iff SATBits circuitBitEncoding.
P01 remaining: preserving unary-index input case, global evalRun refinement, integrated physical verifier.
G21: G21Pointwise (equivalent to P02Target / G22Contradiction in referenced bridge); no unconditional inhabitant certified.
No terminal OPEN_MATH=false or CLOSED_MATH=true assertion is made here.
-/
