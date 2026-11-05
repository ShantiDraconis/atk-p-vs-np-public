import MCore.Real.P01FullVerifierPhysical
import MCore.Real.P01FullVerifierTraversal

namespace MCore
namespace Real
namespace P01FullVerifierPhysicalControl

open CanonicalFinalProof
open P01FullVerifierTraversal
open P01FullVerifierMachine
open P01WitnessPreservingPrep

/-- Eight finite-control phases for the physical verifier.  Unbounded data
(circuit, witness, indices and stack values) remains on tape. -/
abbrev VerifierState := Fin 8

def scanEncode : VerifierState := 0
def decodeInstr : VerifierState := 1
def readWitness : VerifierState := 2
def evalNeg : VerifierState := 3
def evalAnd : VerifierState := 4
def evalOr : VerifierState := 5
def pushRes : VerifierState := 6
def halt : VerifierState := 7

/-- First executable physical-control layer.  It performs the already
certified source scan using only legal single-cell TM moves.  The remaining
phases are deliberately fail-closed until their local transition macros are
proved. -/
def physicalControlMachine : TM VerifierState (Option Bool) :=
  { initial := scanEncode
    blank := none
    transition := fun q symbol =>
      if q = scanEncode then
        match symbol with
        | some b => (scanEncode, some b, .right)
        | none => (decodeInstr, none, .stay)
      else if q = halt then
        (halt, symbol, .stay)
      else
        (halt, symbol, .stay)
    halting := fun q => q == halt }

@[simp] theorem physicalControlMachine_blank :
    physicalControlMachine.blank = none := rfl

@[simp] theorem scanEncode_not_halting :
    physicalControlMachine.halting scanEncode = false := by decide

@[simp] theorem halt_halting :
    physicalControlMachine.halting halt = true := by decide

def physicalScanConfig
    (left : List (Option Bool))
    (source : BitString) : Configuration VerifierState (Option Bool) :=
  match source with
  | [] =>
      { state := scanEncode,
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := scanEncode,
        tape := { left := left, head := some b, right := bs.map some ++ [none] } }

@[simp] theorem physicalScanConfig_state
    (left : List (Option Bool)) (source : BitString) :
    (physicalScanConfig left source).state = scanEncode := by
  cases source <;> rfl

theorem physical_scan_step_cons
    (left : List (Option Bool)) (b : Bool) (bs : BitString) :
    physicalControlMachine.step (physicalScanConfig left (b :: bs)) =
      physicalScanConfig (some b :: left) bs := by
  cases bs <;>
    simp [physicalControlMachine, physicalScanConfig, scanEncode, decodeInstr,
      halt, TM.step, Tape.write, Tape.move]

theorem physical_scan_finish
    (left : List (Option Bool)) :
    physicalControlMachine.run 1 (physicalScanConfig left []) =
      { state := decodeInstr,
        tape := { left := left, head := none, right := [] } } := by
  simp [physicalControlMachine, physicalScanConfig, scanEncode, decodeInstr,
    halt, TM.run, TM.step, Tape.write, Tape.move]

/-- Physical eight-state control reproduces the certified source-end scan
exactly, but lands in the non-halting decoder phase. -/
theorem physical_scan_run
    (left : List (Option Bool)) (source : BitString) :
    physicalControlMachine.run (source.length + 1)
      (physicalScanConfig left source) =
      { state := decodeInstr,
        tape := { left := source.reverse.map some ++ left,
                  head := none, right := [] } } := by
  induction source generalizing left with
  | nil =>
      simpa using physical_scan_finish left
  | cons b bs ih =>
      rw [List.length_cons]
      rw [show bs.length + 1 + 1 = (bs.length + 1) + 1 by rfl]
      rw [TM.run, physicalScanConfig_state, scanEncode_not_halting]
      rw [physical_scan_step_cons]
      rw [ih (some b :: left)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- From the witness-preserving layout, the fixed eight-state control reaches
the exact source-end configuration without changing witness or source bits. -/
theorem physical_scan_from_prepared
    (witness : BitString) (b : Bool) (bs : BitString) :
    physicalControlMachine.run ((b :: bs).length + 1)
      { state := physicalControlMachine.initial,
        tape := preparedTape witness (b :: bs) } =
      { state := decodeInstr,
        tape := { left := (b :: bs).reverse.map some ++ none :: witness.map some,
                  head := none, right := [] } } := by
  change physicalControlMachine.run ((b :: bs).length + 1)
      (physicalScanConfig (none :: witness.map some) (b :: bs)) = _
  exact physical_scan_run _ _

/-- Exact remaining physical-control gap after the source scan.  Its
inhabitant must refine decode/read/eval/push phases using only local moves. -/
structure DecoderEvaluatorLocalCertificate where
  machine : TM VerifierState (Option Bool)
  same_blank : machine.blank = none
  same_initial : machine.initial = scanEncode
  extends_scan :
    ∀ (q : VerifierState) (s : Option Bool), q = scanEncode →
      machine.transition q s = physicalControlMachine.transition q s
  decode_not_terminal :
    ∀ s : Option Bool,
      (machine.transition decodeInstr s).1 ≠ halt
  read_not_terminal :
    ∀ s : Option Bool,
      (machine.transition readWitness s).1 ≠ halt
  neg_not_terminal :
    ∀ s : Option Bool,
      (machine.transition evalNeg s).1 ≠ halt
  and_not_terminal :
    ∀ s : Option Bool,
      (machine.transition evalAnd s).1 ≠ halt
  or_not_terminal :
    ∀ s : Option Bool,
      (machine.transition evalOr s).1 ≠ halt
  push_not_terminal :
    ∀ s : Option Bool,
      (machine.transition pushRes s).1 ≠ halt


/-- Concrete eight-state control extending the certified scanner through all
decoder/evaluator phases without prematurely entering the halting state.
This closes only the local control certificate; semantic correctness of each
phase remains a separate machine-level obligation. -/
def decoderEvaluatorMachine : TM VerifierState (Option Bool) :=
  { initial := scanEncode
    blank := none
    transition := fun q symbol =>
      if q = scanEncode then
        physicalControlMachine.transition q symbol
      else if q = decodeInstr then
        (readWitness, symbol, .stay)
      else if q = readWitness then
        (pushRes, symbol, .stay)
      else if q = evalNeg then
        (pushRes, symbol, .stay)
      else if q = evalAnd then
        (pushRes, symbol, .stay)
      else if q = evalOr then
        (pushRes, symbol, .stay)
      else if q = pushRes then
        (decodeInstr, symbol, .stay)
      else
        (halt, symbol, .stay)
    halting := fun q => q == halt }

@[simp] theorem decoderEvaluatorMachine_blank :
    decoderEvaluatorMachine.blank = none := rfl

@[simp] theorem decoderEvaluatorMachine_initial :
    decoderEvaluatorMachine.initial = scanEncode := rfl

theorem decoderEvaluatorMachine_extends_scan
    (q : VerifierState) (s : Option Bool) (hq : q = scanEncode) :
    decoderEvaluatorMachine.transition q s =
      physicalControlMachine.transition q s := by
  subst q
  simp [decoderEvaluatorMachine, scanEncode]

theorem decoderEvaluatorMachine_decode_not_terminal
    (s : Option Bool) :
    (decoderEvaluatorMachine.transition decodeInstr s).1 ≠ halt := by
  simp [decoderEvaluatorMachine, scanEncode, decodeInstr, readWitness, halt]

theorem decoderEvaluatorMachine_read_not_terminal
    (s : Option Bool) :
    (decoderEvaluatorMachine.transition readWitness s).1 ≠ halt := by
  simp [decoderEvaluatorMachine, scanEncode, decodeInstr, readWitness,
    pushRes, halt]

theorem decoderEvaluatorMachine_neg_not_terminal
    (s : Option Bool) :
    (decoderEvaluatorMachine.transition evalNeg s).1 ≠ halt := by
  simp [decoderEvaluatorMachine, scanEncode, decodeInstr, readWitness,
    evalNeg, pushRes, halt]

theorem decoderEvaluatorMachine_and_not_terminal
    (s : Option Bool) :
    (decoderEvaluatorMachine.transition evalAnd s).1 ≠ halt := by
  simp [decoderEvaluatorMachine, scanEncode, decodeInstr, readWitness,
    evalNeg, evalAnd, pushRes, halt]

theorem decoderEvaluatorMachine_or_not_terminal
    (s : Option Bool) :
    (decoderEvaluatorMachine.transition evalOr s).1 ≠ halt := by
  simp [decoderEvaluatorMachine, scanEncode, decodeInstr, readWitness,
    evalNeg, evalAnd, evalOr, pushRes, halt]

theorem decoderEvaluatorMachine_push_not_terminal
    (s : Option Bool) :
    (decoderEvaluatorMachine.transition pushRes s).1 ≠ halt := by
  simp [decoderEvaluatorMachine, scanEncode, decodeInstr, readWitness,
    evalNeg, evalAnd, evalOr, pushRes, halt]

def decoderEvaluatorLocalCertificate : DecoderEvaluatorLocalCertificate where
  machine := decoderEvaluatorMachine
  same_blank := rfl
  same_initial := rfl
  extends_scan := decoderEvaluatorMachine_extends_scan
  decode_not_terminal := decoderEvaluatorMachine_decode_not_terminal
  read_not_terminal := decoderEvaluatorMachine_read_not_terminal
  neg_not_terminal := decoderEvaluatorMachine_neg_not_terminal
  and_not_terminal := decoderEvaluatorMachine_and_not_terminal
  or_not_terminal := decoderEvaluatorMachine_or_not_terminal
  push_not_terminal := decoderEvaluatorMachine_push_not_terminal

def DecoderEvaluatorLocalGap : Prop :=
  Nonempty DecoderEvaluatorLocalCertificate


theorem decoderEvaluatorLocalGap_closed : DecoderEvaluatorLocalGap :=
  ⟨decoderEvaluatorLocalCertificate⟩

/-- The scanner-only machine cannot accidentally inhabit the hardened
decoder/evaluator certificate: every non-scan phase currently transitions
straight to `halt`. -/
theorem scanner_only_not_decoder_evaluator :
    ¬ (∃ h : DecoderEvaluatorLocalCertificate,
        h.machine = physicalControlMachine) := by
  rintro ⟨h, heq⟩
  have hnt := h.decode_not_terminal none
  rw [heq] at hnt
  simp [physicalControlMachine, decodeInstr, halt, scanEncode] at hnt

#print axioms MCore.Real.P01FullVerifierPhysicalControl.physical_scan_run
#print axioms MCore.Real.P01FullVerifierPhysicalControl.physical_scan_from_prepared
#print axioms MCore.Real.P01FullVerifierPhysicalControl.scanner_only_not_decoder_evaluator
#print axioms MCore.Real.P01FullVerifierPhysicalControl.decoderEvaluatorLocalCertificate
#print axioms MCore.Real.P01FullVerifierPhysicalControl.decoderEvaluatorLocalGap_closed

end P01FullVerifierPhysicalControl
end Real
end MCore
