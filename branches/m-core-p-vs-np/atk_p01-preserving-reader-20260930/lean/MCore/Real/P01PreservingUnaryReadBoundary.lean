import MCore.Real.P01WitnessIndexedReadGlobal
import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01EncodedStackEvaluator

namespace MCore
namespace Real
namespace P01PreservingUnaryReadBoundary

open CanonicalFinalProof
open CanonicalSATWitness
open P01WitnessIndexedRead
open P01WitnessIndexedReadMachine
open P01WitnessIndexedReadGlobal
open P01EvalCursorMachine
open P01EncodedStackEvaluator

/-- Evidence that the existing indexed reader is intrinsically destructive:
one unary successor marker removes the first witness cell and replaces it by
two blank cells in the physical counter region. -/
theorem old_reader_consumes_witness_prefix
    (pad n : Nat) (b : Bool) (tail : BitString) :
    witnessIndexedReadMachine.run (2 * pad + 3)
      (markerConfig pad (b :: tail) (n + 1)) =
      markerConfig (pad + 2) tail n :=
  marker_succ_run pad n b tail

/-- Concrete non-preservation witness for the legacy reader.  After one unary
successor step, the first witness cell has been physically removed from the
witness region. -/
theorem old_reader_not_preserving_example :
    (witnessIndexedReadMachine.run 3
      (markerConfig 0 [false, true] 1)).tape ≠
      (markerConfig 0 [false, true] 1).tape := by
  rw [old_reader_consumes_witness_prefix]
  simp [markerConfig, encodeNat]

/-- Exact source width of one canonical input node. -/
def inputNodeWidth (i : Nat) : Nat := 3 + (encodeNat i).length

/-- Physical start configuration for an input node at the streaming cursor. -/
def inputStartConfig
    {Q : Type} [Inhabited Q]
    (q0 : Q)
    (witness : BitString)
    (consumed i : Nat)
    (rest frameStack : BitString)
    (padding : Nat) : Configuration Q (Option Bool) :=
  { state := q0
    tape := evalCursorStackEndTape witness consumed
      (false :: false :: false :: encodeNat i ++ rest)
      frameStack padding }

/-- Exact tape that must remain after an input node is evaluated.  The witness
and continuation frame stack are byte-for-byte unchanged; only the source
cursor advances past tag 000 and the unary index. -/
def inputFinalTape
    (witness : BitString)
    (consumed i : Nat)
    (rest frameStack : BitString)
    (padding : Nat) : Tape (Option Bool) :=
  evalCursorStackEndTape witness
    (consumed + inputNodeWidth i) rest frameStack padding

/-- Material certificate for the sole remaining local evalStep case.

No index, witness, source, or frame stack is stored in the finite-control type.
The terminal value is read from finite control only after a fixed machine has
processed the tape data. -/
structure PreservingUnaryReadCertificate where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  terminalValue : Fin (stateCount + 1) → Option Bool
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound

  halts :
    ∀ (witness : BitString) (consumed i : Nat)
      (rest frameStack : BitString) (padding : Nat),
      machine.HaltsWithin
        (timeBound
          (witness.length + consumed + inputNodeWidth i +
            rest.length + frameStack.length + padding))
        (inputStartConfig machine.initial witness consumed i
          rest frameStack padding)

  value_correct :
    ∀ (witness : BitString) (consumed i : Nat)
      (rest frameStack : BitString) (padding : Nat)
      (hi : i < witness.length),
      terminalValue
        (machine.run
          (timeBound
            (witness.length + consumed + inputNodeWidth i +
              rest.length + frameStack.length + padding))
          (inputStartConfig machine.initial witness consumed i
            rest frameStack padding)).state =
        some (witness.getD i false)

  tape_preserved :
    ∀ (witness : BitString) (consumed i : Nat)
      (rest frameStack : BitString) (padding : Nat)
      (hi : i < witness.length),
      (machine.run
        (timeBound
          (witness.length + consumed + inputNodeWidth i +
            rest.length + frameStack.length + padding))
        (inputStartConfig machine.initial witness consumed i
          rest frameStack padding)).tape =
        inputFinalTape witness consumed i rest frameStack padding

/-- The exact local open-math/implementation obligation. -/
def PreservingUnaryReadGap : Prop :=
  Nonempty PreservingUnaryReadCertificate

/-- Once the physical certificate exists, the semantic input-node result is
forced to agree with the streaming evaluator's assignment lookup. -/
theorem certificate_refines_input_value
    (C : PreservingUnaryReadCertificate)
    (witness : BitString) (consumed i : Nat)
    (rest frameStack : BitString) (padding : Nat)
    (hi : i < witness.length) :
    C.terminalValue
      (C.machine.run
        (C.timeBound
          (witness.length + consumed + inputNodeWidth i +
            rest.length + frameStack.length + padding))
        (inputStartConfig C.machine.initial witness consumed i
          rest frameStack padding)).state =
      some (witness.getD i false) :=
  C.value_correct witness consumed i rest frameStack padding hi

/-- The same certificate supplies the stronger physical invariant required by
global composition: repeated reads are safe because the witness region and all
unread source/frame data are restored exactly. -/
theorem certificate_preserves_global_layout
    (C : PreservingUnaryReadCertificate)
    (witness : BitString) (consumed i : Nat)
    (rest frameStack : BitString) (padding : Nat)
    (hi : i < witness.length) :
    (C.machine.run
      (C.timeBound
        (witness.length + consumed + inputNodeWidth i +
          rest.length + frameStack.length + padding))
      (inputStartConfig C.machine.initial witness consumed i
        rest frameStack padding)).tape =
      inputFinalTape witness consumed i rest frameStack padding :=
  C.tape_preserved witness consumed i rest frameStack padding hi

#print axioms MCore.Real.P01PreservingUnaryReadBoundary.old_reader_consumes_witness_prefix
#print axioms MCore.Real.P01PreservingUnaryReadBoundary.certificate_refines_input_value
#print axioms MCore.Real.P01PreservingUnaryReadBoundary.certificate_preserves_global_layout

end P01PreservingUnaryReadBoundary
end Real
end MCore
