import MCore.Real.P01RawTotalizationMinCut
import MCore.Real.P01RawDecodeInduction
import MCore.Real.P01RawDecoderSound
import MCore.Real.P01RawResidualReject
import MCore.Real.P01ExactBoundedReject
import MCore.Real.P01RawVerifierLift
import MCore.Real.P01CheckedVerifierDeterminism

namespace MCore
namespace Real
namespace P01RawTotalizationProducer

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01EncodedFrameTape
open P01WitnessPreservingPrep
open P01CheckedVerifierInvariant
open P01CheckedVerifierBudget
open P01CheckedVerifierGlobalBudget
open P01CheckedEvalRunBoundedCertificate
open P01CheckedEvalRunBoundedHelpers
open P01ExactVerifierGlobalBudget
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierDeterminism
open P01ExactBoundedCircuitProducer
open P01ExactBoundedReject
open P01RawResidualReject
open P01RawDeadEnd
open P01RawVerifierLift
open P01RawEvalSink
open P01RawRecursiveBudget
open P01RawRecursiveSteps
open P01RawDecodeInduction
open P01RawTotalizationMinCut
open P01NTMRunLaws

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

abbrev VerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

/-- Promote any already fail-closed verifier run to the common quartic raw
fuel. -/
theorem promote_fail_closed_to_raw
    (source witness : BitString)
    (t : Nat)
    (ht : t ≤ checkedVerifierRawTimeBound source.length)
    (hhalt :
      checkedVerifierMachine.HaltsWithin t
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source })
    (hnot :
      ¬ checkedVerifierMachine.AcceptsWithin t
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source }) :
    checkedVerifierMachine.HaltsWithin
        (checkedVerifierRawTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierRawTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  let start : VerifierConfig :=
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness source }
  have hh :=
    haltsWithin_mono_le checkedVerifierMachine
      t (checkedVerifierRawTimeBound source.length)
      start ht (by simpa [start] using hhalt)
  have hn :=
    not_acceptsWithin_mono_after_halt
      t (checkedVerifierRawTimeBound source.length)
      start ht (by simpa [start] using hhalt)
      (by simpa [start] using hnot)
  exact ⟨by simpa [start] using hh, by simpa [start] using hn⟩

/-- Lift one evaluator failure sink on a nonempty source to full-verifier
fail-closed behavior at the quartic raw fuel. -/
theorem prepared_nonempty_sink_fail_closed_raw
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (m : Nat) (target : EvalConfig)
    (hm :
      m ≤ rawFailureBudget ((b :: bs).length + 1) (b :: bs).length)
    (hreach :
      target ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := checkedEvalRunLoopMachine.initial,
           tape :=
             evalCursorStackEndTape witness 0 (b :: bs) [] 0 }])
    (hsink : EvalFailureSink target) :
    checkedVerifierMachine.HaltsWithin
        (checkedVerifierRawTimeBound (b :: bs).length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierRawTimeBound (b :: bs).length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } := by
  obtain ⟨m0, hm0, hfull⟩ :=
    prepared_nonempty_lift_eval_reach
      witness b bs m target hreach
  let start : VerifierConfig :=
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness (b :: bs) }
  let lifted : VerifierConfig :=
    P01NTMRunLaws.liftConfig checkedEvalEmbed target
  have hfull' :
      lifted ∈ checkedVerifierMachine.runBranches (m0 + m) [start] := by
    simpa [start, lifted] using hfull
  cases hsink with
  | reject hstate =>
      have hstateV : lifted.state = .reject := by
        dsimp [lifted, P01NTMRunLaws.liftConfig]
        rw [hstate]
        rfl
      have hhaltLift : P01NTMRunLaws.Halted checkedVerifierMachine lifted := by
        unfold P01NTMRunLaws.Halted
        rw [hstateV]
        simp [checkedVerifierMachine]
      have hhSmall :
          checkedVerifierMachine.HaltsWithin (m0 + m) start :=
        P01CheckedVerifierDeterminism.haltsWithin_of_reaches_halted
          (m0 + m) start lifted hfull' hhaltLift
      have hnSmall :
          ¬ checkedVerifierMachine.AcceptsWithin (m0 + m) start := by
        intro hacc
        rcases hacc with ⟨z, hz, hzacc⟩
        have heq :=
          P01CheckedVerifierDeterminism.runBranches_eq_singleton_of_mem
            (m0 + m) start lifted hfull'
        rw [heq] at hz
        simp only [List.mem_singleton] at hz
        subst z
        rw [hstateV] at hzacc
        simp [checkedVerifierMachine] at hzacc
      have htotal :
          m0 + m ≤ checkedVerifierRawTimeBound (b :: bs).length := by
        have hscan :
            m0 ≤ rawChunk (b :: bs).length :=
          Nat.le_trans hm0
            (scanLinear_le_rawChunk (b :: bs).length)
        have hsum :
            m0 + m ≤
              rawFailureBudget ((b :: bs).length + 1) (b :: bs).length +
                rawChunk (b :: bs).length := by
          omega
        exact Nat.le_trans hsum
          (rootFailure_plus_chunk_le_rawTimeBound (b :: bs).length)
      exact promote_fail_closed_to_raw
        (b :: bs) witness (m0 + m) htotal
        (by simpa [start] using hhSmall)
        (by simpa [start] using hnSmall)
  | dead hactive hdead =>
      have hVdead :=
        lifted_eval_dead_is_verifier_dead target hactive hdead
      have hhSmall :
          checkedVerifierMachine.HaltsWithin (m0 + m + 1) start :=
        haltsWithin_succ_of_reaches_dead
          (m0 + m) start lifted hfull'
          hVdead.1 hVdead.2
      have hnSmall :
          ¬ checkedVerifierMachine.AcceptsWithin (m0 + m + 1) start :=
        not_acceptsWithin_succ_of_reaches_dead
          (m0 + m) start lifted hfull'
          hVdead.1 hVdead.2
      have hscan1 :
          m0 + 1 ≤ rawChunk (b :: bs).length := by
        exact Nat.le_trans (by omega)
          (scanPlusOne_le_rawChunk (b :: bs).length)
      have htotal :
          m0 + m + 1 ≤
            checkedVerifierRawTimeBound (b :: bs).length := by
        have hsum :
            m0 + m + 1 ≤
              rawFailureBudget ((b :: bs).length + 1) (b :: bs).length +
                rawChunk (b :: bs).length := by
          omega
        exact Nat.le_trans hsum
          (rootFailure_plus_chunk_le_rawTimeBound (b :: bs).length)
      exact promote_fail_closed_to_raw
        (b :: bs) witness (m0 + m + 1) htotal
        (by simpa [start] using hhSmall)
        (by simpa [start] using hnSmall)

/-- Empty source is already fail-closed at cubic fuel, hence also at the raw
quartic fuel. -/
theorem prepared_empty_fail_closed_raw
    (witness : BitString) :
    checkedVerifierMachine.HaltsWithin
        (checkedVerifierRawTimeBound 0)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierRawTimeBound 0)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] } := by
  have h :=
    P01RawBaseExact.prepared_empty_fail_closed_exact witness
  exact promote_fail_closed_to_raw
    [] witness (checkedVerifierExactTimeBound 0)
    (exactTimeBound_le_rawTimeBound 0) h.1 h.2

private theorem canonical_prefix_layout
    (source witness : BitString)
    (phi : Circuit)
    (tail : BitString)
    (hsrc : source = encodeCircuit phi ++ tail) :
    CheckedLayoutBound source.length 0
      (encodeCircuit phi ++ tail) (encodeEvalFrames []) := by
  subst source
  constructor <;> simp

private theorem canonical_prefix_varBound
    (source witness : BitString)
    (phi : Circuit)
    (tail : BitString)
    (hw : witness.length = source.length)
    (hsrc : source = encodeCircuit phi ++ tail) :
    varBound phi ≤ witness.length := by
  rw [hw, hsrc]
  have hv := varBound_le_encoded_length phi
  simp [List.length_append]
  omega

private theorem canonical_prefix_enc_len
    (source : BitString)
    (phi : Circuit)
    (tail : BitString)
    (hsrc : source = encodeCircuit phi ++ tail) :
    (encodeCircuit phi).length ≤ source.length := by
  rw [hsrc, List.length_append]
  omega

/-- Whole-source decoder failure is physically fail-closed.  This is the
material inhabitant of the sole remaining P01 mechanical min-cut. -/
theorem decodeCircuit_none_fail_closed_raw
    (source witness : BitString)
    (hw : witness.length = source.length)
    (hdec : decodeCircuit source = none) :
    checkedVerifierMachine.HaltsWithin
        (checkedVerifierRawTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierRawTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  cases source with
  | nil =>
      exact prepared_empty_fail_closed_raw witness
  | cons b bs =>
      let source : BitString := b :: bs
      cases hc :
          decodeCircuitCore (source.length + 1) source with
      | none =>
          have hLayout :
              CheckedLayoutBound source.length 0 source
                (encodeEvalFrames []) := by
            exact P01CheckedVerifierInvariant.root source
          have hsink :=
            decodeCore_none_reaches_sink
              (source.length + 1) source
              (Nat.lt_succ_self source.length)
              (by simpa using hc)
              .cnf witness [] 0 0 source.length
              (by simpa [source] using hw)
              hLayout
          rcases hsink with ⟨m, hm, target, hreach, hs⟩
          exact prepared_nonempty_sink_fail_closed_raw
            witness b bs m target
            (by simpa [source] using hm)
            (by simpa [source, encodeEvalFrames] using hreach)
            hs
      | some p =>
          rcases p with ⟨phi, tail⟩
          cases tail with
          | nil =>
              have hsome :
                  decodeCircuit source = some phi := by
                simp [decodeCircuit, hc]
              rw [hdec] at hsome
              cases hsome
          | cons rb rtail =>
              let residual : BitString := rb :: rtail
              have hcore :
                  decodeCircuitCore (source.length + 1) source =
                    some (phi, residual) := by
                simpa [residual] using hc
              have hsrc :
                  source = encodeCircuit phi ++ residual :=
                P01RawDecoderSound.decodeCircuitCore_success_sound
                  (source.length + 1) source phi residual hcore
              have hLayout :
                  CheckedLayoutBound source.length 0
                    (encodeCircuit phi ++ residual)
                    (encodeEvalFrames []) :=
                canonical_prefix_layout source witness phi residual hsrc
              have hlen :
                  varBound phi ≤ witness.length :=
                canonical_prefix_varBound
                  source witness phi residual
                  (by simpa [source] using hw) hsrc
              have henc :
                  (encodeCircuit phi).length ≤ source.length :=
                canonical_prefix_enc_len source phi residual hsrc
              cases hmode : modeCheck .cnf phi with
              | false =>
                  have hreject :=
                    circuit_exact_bounded_reject
                      (P01RawRecursiveSteps.witnessAssignment witness) witness phi .cnf
                  obtain ⟨m, hm, cfg, hreach, hstate⟩ :=
                    hreject hmode residual [] 0 0 source.length
                      (by simpa [encodeEvalFrames] using hLayout)
                      hlen (by intro i hi; rfl)
                  have hbudget :
                      m ≤ rawFailureBudget (source.length + 1)
                        source.length := by
                    have hcirc :=
                      checkedCircuitBudget_le_exact_global
                        source.length phi henc
                    have hmChunk : m ≤ rawChunk source.length := by
                      have h6144 :
                          6144 * (source.length + 1) ^ 3 ≤
                            rawChunk source.length := by
                        unfold rawChunk checkedVerifierExactTimeBound
                        exact Nat.mul_le_mul_right
                          ((source.length + 1) ^ 3) (by omega)
                      exact Nat.le_trans hm
                        (Nat.le_trans hcirc h6144)
                    exact Nat.le_trans hmChunk
                      (rawChunk_le_failureBudget
                        (source.length + 1) source.length (by omega))
                  exact prepared_nonempty_sink_fail_closed_raw
                    witness b bs m cfg
                    (by simpa [source] using hbudget)
                    (by simpa [source, hsrc, encodeEvalFrames] using hreach)
                    (.reject hstate)
              | true =>
                  obtain ⟨m, hm, cfg, hreach, hstate⟩ :=
                    canonical_prefix_with_residual_reaches_reject
                      (P01RawRecursiveSteps.witnessAssignment witness) witness phi residual
                      (by simp [residual]) hmode source.length
                      (by simpa [encodeEvalFrames] using hLayout)
                      hlen (by intro i hi; rfl)
                  have h3 :
                      3 ≤ checkedLoopStepEnvelope source.length := by
                    exact Nat.le_trans (by omega)
                      (nine_le_stepEnvelope source.length)
                  have hcost :
                      checkedCircuitBudget phi source.length + 3 ≤
                        rawChunk source.length := by
                    have hc :=
                      circuit_plus_loop_le_rawChunk
                        source.length phi henc
                    omega
                  have hmChunk : m ≤ rawChunk source.length :=
                    Nat.le_trans hm hcost
                  have hbudget :
                      m ≤ rawFailureBudget (source.length + 1)
                        source.length :=
                    Nat.le_trans hmChunk
                      (rawChunk_le_failureBudget
                        (source.length + 1) source.length (by omega))
                  exact prepared_nonempty_sink_fail_closed_raw
                    witness b bs m cfg
                    (by simpa [source] using hbudget)
                    (by simpa [source, hsrc, encodeEvalFrames] using hreach)
                    (.reject hstate)

/-- Concrete inhabitant of the exact remaining P01 raw-totalization structure. -/
def rawDecodeNoneFailClosedProducer :
    RawDecodeNoneFailClosed where
  halts := by
    intro bs w hw hdec
    exact (decodeCircuit_none_fail_closed_raw bs w hw hdec).1
  rejects := by
    intro bs w hw hdec
    exact (decodeCircuit_none_fail_closed_raw bs w hw hdec).2

/-- P01 is mechanically closed once the raw producer above kernel-checks. -/
theorem p01ConstructionGap_closed :
    P01FinalCertificate.P01ConstructionGap :=
  p01ConstructionGap_of_rawDecodeNoneFailClosed
    rawDecodeNoneFailClosedProducer

#print axioms MCore.Real.P01RawTotalizationProducer.decodeCircuit_none_fail_closed_raw
#print axioms MCore.Real.P01RawTotalizationProducer.rawDecodeNoneFailClosedProducer
#print axioms MCore.Real.P01RawTotalizationProducer.p01ConstructionGap_closed

end P01RawTotalizationProducer
end Real
end MCore
