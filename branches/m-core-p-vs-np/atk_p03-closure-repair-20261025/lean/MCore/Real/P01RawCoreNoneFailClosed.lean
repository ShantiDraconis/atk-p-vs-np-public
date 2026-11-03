import MCore.Real.P01RawRecursiveClosure
import MCore.Real.P01RawPreparedRejectLift
import MCore.Real.P01RawRecursiveBudget
import MCore.Real.P01RawDeadEnd

namespace MCore
namespace Real
namespace P01RawCoreNoneFailClosed

open CanonicalFinalProof
open CanonicalCircuitBits
open P01CheckedVerifierCompositeNTM
open P01WitnessPreservingPrep
open P01RawEvalSink
open P01RawRecursiveSteps
open P01RawRecursiveClosure
open P01RawPreparedRejectLift
open P01RawRecursiveBudget
open P01RawDeadEnd
open P01NTMRunLaws

abbrev VerifierConfig :=
  Configuration P01CheckedVerifierCompositeNTM.CheckedVerifierState
    (Option Bool)

/-- Promote any already-established fail-closed verifier fuel to the final
quartic raw budget. -/
theorem promote_fail_closed_raw
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

/-- Every whole-source recursive decoder failure is fail-closed in the complete
prepared verifier at one uniform quartic polynomial fuel. -/
theorem prepared_core_none_fail_closed_raw
    (bits witness : BitString)
    (hw : witness.length = bits.length)
    (hcore :
      decodeCircuitCore (bits.length + 1) bits = none) :
    checkedVerifierMachine.HaltsWithin
        (checkedVerifierRawTimeBound bits.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness bits } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierRawTimeBound bits.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness bits } := by
  cases hbits : bits with
  | nil =>
      have hbase :=
        prepared_empty_reject_fail_closed witness
      have hle : 1 ≤ checkedVerifierRawTimeBound 0 := by
        decide
      simpa [hbits] using
        promote_fail_closed_raw [] witness 1 hle hbase.1 hbase.2
  | cons b bs =>
      have hsink :=
        root_core_none_reaches_sink (b :: bs) witness
          (by simpa [hbits] using hw)
          (by simpa [hbits] using hcore)
      rcases hsink with ⟨m, hm, cfg, hreach, hs⟩
      cases hs with
      | reject hstate =>
          obtain ⟨total, htotal, hh, hn⟩ :=
            prepared_nonempty_reject_fail_closed
              witness b bs m cfg hreach hstate
          have hscan :
              (b :: bs).length + 3 + m ≤
                rawChunk (b :: bs).length +
                  rawFailureBudget ((b :: bs).length + 1)
                    (b :: bs).length := by
            have hs := scanLinear_le_rawChunk (b :: bs).length
            omega
          have hroot :=
            rootFailure_plus_chunk_le_rawTimeBound (b :: bs).length
          have hle :
              total ≤ checkedVerifierRawTimeBound (b :: bs).length := by
            omega
          have hp :=
            promote_fail_closed_raw (b :: bs) witness total
              hle hh hn
          simpa [hbits] using hp
      | dead hactive hdead =>
          obtain ⟨total, htotal, hh, hn⟩ :=
            P01RawVerifierLift.prepared_nonempty_dead_fail_closed
              witness b bs m cfg hreach hactive hdead
          have hscan :
              (b :: bs).length + 3 + m + 1 ≤
                rawChunk (b :: bs).length +
                  rawFailureBudget ((b :: bs).length + 1)
                    (b :: bs).length := by
            have hs := scanPlusOne_le_rawChunk (b :: bs).length
            omega
          have hroot :=
            rootFailure_plus_chunk_le_rawTimeBound (b :: bs).length
          have hle :
              total ≤ checkedVerifierRawTimeBound (b :: bs).length := by
            omega
          have hp :=
            promote_fail_closed_raw (b :: bs) witness total
              hle hh hn
          simpa [hbits] using hp

#print axioms MCore.Real.P01RawCoreNoneFailClosed.promote_fail_closed_raw
#print axioms MCore.Real.P01RawCoreNoneFailClosed.prepared_core_none_fail_closed_raw

end P01RawCoreNoneFailClosed
end Real
end MCore
