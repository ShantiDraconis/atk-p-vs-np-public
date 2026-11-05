import MCore.Real.P01RawMalformedProducer
import MCore.Real.P01RawResidualReject
import MCore.Real.P01RawVerifierFailClosed
import MCore.Real.P01RawMalformedRecursiveRight
import MCore.Real.P01ExactBoundedReject
import MCore.Real.P01GuessedWitnessRelation

namespace MCore
namespace Real
namespace P01RawMalformedVerifier

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open P01CNFMode
open P01EncodedStackEvaluator
open P01CheckedVerifierInvariant
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierCompositeNTM
open P01CheckedEvalRunBoundedCertificate
open P01ExactBoundedCircuitProducer
open P01ExactBoundedReject
open P01RawTotalContract
open P01RawMalformedProducer
open P01RawMalformedBaseProducer
open P01RawMalformedRecursiveRight
open P01RawResidualReject
open P01RawVerifierFailClosed
open P01WitnessPreservingPrep

def rawVerifierRejectBound (n : Nat) : Nat :=
  n + 8 + rawMalformedBudget (n + 1) n

theorem circuitBudget_le_rawSlice
    (phi : CircuitK1.Circuit)
    (n : Nat)
    (henc : (encodeCircuit phi).length ≤ n) :
    checkedCircuitBudget phi n ≤ rawMalformedSlice n := by
  have h :=
    checkedCircuitBudget_plus_one_loop_le_slice phi n henc
  omega

theorem rawSlice_le_topBudget (n : Nat) :
    rawMalformedSlice n ≤ rawMalformedBudget (n + 1) n :=
  slice_le_rawMalformedBudget (n + 1) n

/-- Exact fail-closed theorem for every raw source rejected by the canonical
whole-source decoder. -/
theorem raw_malformed_reject_bounded
    (witness bs : BitString)
    (hwitness : bs.length ≤ witness.length)
    (hdecode : decodeCircuit bs = none) :
    ∃ t ≤ rawVerifierRejectBound bs.length,
      checkedVerifierMachine.HaltsWithin t
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness bs } ∧
      ¬ checkedVerifierMachine.AcceptsWithin t
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness bs } := by
  cases bs with
  | nil =>
      obtain ⟨t, ht, hhalt, hnot⟩ :=
        prepared_empty_fail_closed witness
      refine ⟨t, ?_, ?_, ?_⟩
      · unfold rawVerifierRejectBound
        simp
        omega
      · simpa using hhalt
      · simpa using hnot
  | cons b bsTail =>
      let source : BitString := b :: bsTail
      cases hcore :
          decodeCircuitCore (source.length + 1) source with
      | none =>
          have hRawAt :=
            rawMalformedPhysicalProducer (source.length + 1)
          have hLayout :
              CheckedLayoutBound source.length 0 source
                (encodeEvalFrames []) := by
            simpa using (P01CheckedVerifierInvariant.root source)
          obtain ⟨m, hm, cfg, hreach, hfc⟩ :=
            hRawAt witness source [] .cnf 0 0 source.length
              (by omega) hcore hLayout (by simpa [source] using hwitness)
          have hreach' :
              cfg ∈ checkedEvalRunLoopMachine.runBranches m
                [{ state := checkedEvalRunLoopMachine.initial,
                   tape :=
                     P01EvalCursorMachine.evalCursorStackEndTape
                       witness 0 source [] 0 }] := by
            simpa [checkedEvalRunLoopMachine] using hreach
          obtain ⟨total, htotal, hhalt, hnot⟩ :=
            prepared_nonempty_eval_fail_closed
              witness b bsTail m cfg
              (by simpa [source] using hreach') hfc
          refine ⟨total, ?_, ?_, ?_⟩
          · unfold rawVerifierRejectBound
            dsimp [source] at hm htotal ⊢
            omega
          · simpa [source] using hhalt
          · simpa [source] using hnot
      | some p =>
          rcases p with ⟨phi, tail⟩
          cases tail with
          | nil =>
              unfold decodeCircuit at hdecode
              rw [show (b :: bsTail).length + 1 = source.length + 1 by
                simp [source]] at hdecode
              rw [hcore] at hdecode
              simp at hdecode
          | cons tb ts =>
              let tail : BitString := tb :: ts
              have hsource :
                  source = encodeCircuit phi ++ tail := by
                exact P01GuessedWitnessRelation.decodeCircuitCore_sound
                  (source.length + 1) source phi tail
                  (by simpa [tail] using hcore)
              have henc :
                  (encodeCircuit phi).length ≤ source.length := by
                rw [hsource]
                simp
              have hlen :
                  varBound phi ≤ witness.length := by
                exact Nat.le_trans
                  (P01GuessedWitnessRelation.varBound_le_encoded_length phi)
                  (Nat.le_trans henc (by simpa [source] using hwitness))
              have hread :
                  ∀ i, i < varBound phi →
                    witness.getD i false =
                      P01RawTotalContract.witnessAssignment witness i := by
                intro i hi
                rfl
              have hLayout :
                  CheckedLayoutBound source.length 0
                    (encodeCircuit phi ++ tail) (encodeEvalFrames []) := by
                rw [← hsource]
                simpa using P01CheckedVerifierInvariant.root source
              cases hmode : modeCheck .cnf phi with
              | false =>
                  have hNeg :=
                    circuit_exact_bounded_reject
                      (P01RawTotalContract.witnessAssignment witness)
                      witness phi .cnf
                  obtain ⟨m, hm, cfg, hreach, hrej⟩ :=
                    hNeg hmode tail [] 0 0 source.length
                      hLayout hlen hread
                  have hreach' :
                      cfg ∈ checkedEvalRunLoopMachine.runBranches m
                        [{ state := checkedEvalRunLoopMachine.initial,
                           tape :=
                             P01EvalCursorMachine.evalCursorStackEndTape
                               witness 0 source [] 0 }] := by
                    rw [hsource]
                    simpa [checkedEvalRunLoopMachine] using hreach
                  obtain ⟨total, htotal, hhalt, hnot⟩ :=
                    prepared_nonempty_eval_fail_closed
                      witness b bsTail m cfg
                      (by simpa [source] using hreach')
                      (Or.inl hrej)
                  have hmSlice :
                      m ≤ rawMalformedSlice source.length :=
                    Nat.le_trans hm
                      (circuitBudget_le_rawSlice phi source.length henc)
                  have hsliceTop :=
                    rawSlice_le_topBudget source.length
                  refine ⟨total, ?_, ?_, ?_⟩
                  · unfold rawVerifierRejectBound
                    dsimp [source] at htotal hmSlice hsliceTop ⊢
                    omega
                  · simpa [source] using hhalt
                  · simpa [source] using hnot
              | true =>
                  obtain ⟨m, hm, cfg, hreach, hrej⟩ :=
                    canonical_prefix_with_residual_reaches_reject
                      (P01RawTotalContract.witnessAssignment witness)
                      witness phi tail (by simp [tail])
                      hmode source.length hLayout hlen hread
                  have hreach' :
                      cfg ∈ checkedEvalRunLoopMachine.runBranches m
                        [{ state := checkedEvalRunLoopMachine.initial,
                           tape :=
                             P01EvalCursorMachine.evalCursorStackEndTape
                               witness 0 source [] 0 }] := by
                    rw [hsource]
                    simpa using hreach
                  obtain ⟨total, htotal, hhalt, hnot⟩ :=
                    prepared_nonempty_eval_fail_closed
                      witness b bsTail m cfg
                      (by simpa [source] using hreach')
                      (Or.inl hrej)
                  have hcb :
                      checkedCircuitBudget phi source.length ≤
                        rawMalformedSlice source.length :=
                    circuitBudget_le_rawSlice phi source.length henc
                  have hsliceTop :=
                    rawSlice_le_topBudget source.length
                  refine ⟨total, ?_, ?_, ?_⟩
                  · unfold rawVerifierRejectBound
                    dsimp [source] at hm htotal hcb hsliceTop ⊢
                    omega
                  · simpa [source] using hhalt
                  · simpa [source] using hnot

#print axioms MCore.Real.P01RawMalformedVerifier.raw_malformed_reject_bounded

end P01RawMalformedVerifier
end Real
end MCore
