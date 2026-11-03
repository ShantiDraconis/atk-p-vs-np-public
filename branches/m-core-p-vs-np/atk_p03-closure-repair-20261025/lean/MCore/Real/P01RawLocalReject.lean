import MCore.Real.P01RawPreparedRejectLift
import MCore.Real.P01RawResidualReject
import MCore.Real.P01ExactBoundedReject
import MCore.Real.P01RawDecoderSound
import MCore.Real.P01RawDecodeFailureDescent

namespace MCore
namespace Real
namespace P01RawLocalReject

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01NeedExprTagDecode
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierInvariant
open P01ExactBoundedCircuitProducer
open P01ExactBoundedReject
open P01RawResidualReject
open P01RawPreparedRejectLift
open P01RawDecoderSound
open P01RawDecodeFailureDescent
open P01DirectVerifierInhabitant
open P01WitnessPreservingPrep

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Any disallowed three-bit root tag is fail-closed in the complete prepared
verifier, not only in the evaluator submachine. -/
theorem prepared_disallowed_tag_fail_closed
    (witness rest : BitString)
    (b0 b1 b2 : Bool)
    (hdis :
      tagAllowed .cnf (decodeTagBits b0 b1 b2) = false) :
    ∃ total,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b0 :: b1 :: b2 :: rest) } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b0 :: b1 :: b2 :: rest) } := by
  obtain ⟨m, hm, hreach⟩ :=
    disallowed_tag_prefix_reaches_reject
      .cnf witness rest [] 0 0 b0 b1 b2 hdis
  let target : EvalConfig :=
    { state := .reject,
      tape :=
        P01EvalCursorMachine.evalCursorReadTape witness 3 rest [] 0 }
  have hreach' :
      target ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := checkedEvalRunLoopMachine.initial,
           tape :=
             P01EvalCursorMachine.evalCursorStackEndTape witness 0
               (b0 :: b1 :: b2 :: rest) [] 0 }] := by
    simpa [target, checkedEvalRunLoopMachine] using hreach
  obtain ⟨total, htotal, hhalt, hnot⟩ :=
    prepared_nonempty_reject_fail_closed
      witness b0 (b1 :: b2 :: rest) m target hreach' rfl
  exact ⟨total, hhalt, hnot⟩

theorem prepared_invalid110_fail_closed
    (witness rest : BitString) :
    ∃ total,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (true :: true :: false :: rest) } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (true :: true :: false :: rest) } := by
  exact prepared_disallowed_tag_fail_closed
    witness rest true true false rfl

theorem prepared_invalid111_fail_closed
    (witness rest : BitString) :
    ∃ total,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (true :: true :: true :: rest) } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (true :: true :: true :: rest) } := by
  exact prepared_disallowed_tag_fail_closed
    witness rest true true true rfl

/-- A successful decoder prefix followed by residual bits is fail-closed,
whether the decoded prefix is a valid CNF or already syntactically invalid. -/
theorem prepared_residual_fail_closed
    (witness bits : BitString)
    (phi : Circuit) (b : Bool) (tail : BitString)
    (hw : witness.length = bits.length)
    (hcore :
      decodeCircuitCore (bits.length + 1) bits =
        some (phi, b :: tail)) :
    ∃ total,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness bits } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness bits } := by
  have hsrc :
      bits = encodeCircuit phi ++ (b :: tail) :=
    residual_is_canonical_prefix bits phi b tail hcore
  have hlenEnc : (encodeCircuit phi).length ≤ bits.length := by
    rw [hsrc]
    simp [List.length_append]
  have hvar : varBound phi ≤ witness.length := by
    have hv := varBound_le_encoded_length phi
    rw [hw]
    exact Nat.le_trans hv hlenEnc
  have hread :
      ∀ i, i < varBound phi →
        witness.getD i false =
          P01DirectVerifierInhabitant.witnessAssignment witness i := by
    intro i hi
    rfl
  have hLayout :
      CheckedLayoutBound bits.length 0
        (encodeCircuit phi ++ (b :: tail)) [] := by
    rw [← hsrc]
    exact P01CheckedVerifierInvariant.root bits
  cases hmode : modeCheck .cnf phi with
  | true =>
      obtain ⟨m, hm, cfg, hreach, hreject⟩ :=
        canonical_prefix_with_residual_reaches_reject
          (P01DirectVerifierInhabitant.witnessAssignment witness)
          witness phi (b :: tail) (by simp)
          hmode bits.length hLayout hvar hread
      have hreach0 :
          cfg ∈ checkedEvalRunLoopMachine.runBranches m
            [{ state := checkedEvalRunLoopMachine.initial,
               tape :=
                 P01EvalCursorMachine.evalCursorStackEndTape
                   witness 0 bits [] 0 }] := by
        simpa [hsrc] using hreach
      cases hbits : bits with
      | nil =>
          simp [hsrc, encodeCircuit] at hbits
      | cons x xs =>
          obtain ⟨total, htotal, hh, hn⟩ :=
            prepared_nonempty_reject_fail_closed
              witness x xs m cfg
              (by simpa [hbits] using hreach0)
              hreject
          exact ⟨total, by simpa [hbits] using hh,
            by simpa [hbits] using hn⟩
  | false =>
      have hcert :=
        circuit_exact_bounded_reject
          (P01DirectVerifierInhabitant.witnessAssignment witness)
          witness phi .cnf
      obtain ⟨m, hm, cfg, hreach, hreject⟩ :=
        hcert hmode (b :: tail) [] 0 0 bits.length
          hLayout hvar hread
      have hreach0 :
          cfg ∈ checkedEvalRunLoopMachine.runBranches m
            [{ state := checkedEvalRunLoopMachine.initial,
               tape :=
                 P01EvalCursorMachine.evalCursorStackEndTape
                   witness 0 bits [] 0 }] := by
        simpa [hsrc] using hreach
      cases hbits : bits with
      | nil =>
          simp [hsrc, encodeCircuit] at hbits
      | cons x xs =>
          obtain ⟨total, htotal, hh, hn⟩ :=
            prepared_nonempty_reject_fail_closed
              witness x xs m cfg
              (by simpa [hbits] using hreach0)
              hreject
          exact ⟨total, by simpa [hbits] using hh,
            by simpa [hbits] using hn⟩

#print axioms MCore.Real.P01RawLocalReject.prepared_disallowed_tag_fail_closed
#print axioms MCore.Real.P01RawLocalReject.prepared_invalid110_fail_closed
#print axioms MCore.Real.P01RawLocalReject.prepared_invalid111_fail_closed
#print axioms MCore.Real.P01RawLocalReject.prepared_residual_fail_closed

end P01RawLocalReject
end Real
end MCore
