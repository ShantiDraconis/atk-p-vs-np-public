import MCore.Real.P01RawMalformedTag
import MCore.Real.P01RawMalformedUnary
import MCore.Real.P01RawVerifierLift
import MCore.Real.P01RawDecodeFailureShape
import MCore.Real.P01RawDecodeFailureDescent
import MCore.Real.P01ExactVerifierGlobalBudget
import MCore.Real.P01CheckedEvalRunTagPrefix

namespace MCore
namespace Real
namespace P01RawBaseExact

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessPreservingPrep
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierDeterminism
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix
open P01CheckedVerifierBudget
open P01CheckedVerifierGlobalBudget
open P01ExactVerifierGlobalBudget
open P01RawDeadEnd
open P01RawVerifierLift
open P01NTMRunLaws

abbrev VerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- A linear local failure budget is negligible compared with the fixed cubic
global verifier budget. -/
theorem two_mul_add_eleven_le_exact_global (n : Nat) :
    2 * n + 11 ≤ checkedVerifierExactTimeBound n := by
  have h1 : 2 * n + 11 ≤ 11 * (n + 1) := by omega
  have h2 :
      11 * (n + 1) ≤ 11 * ((n + 1) * (n + 1)) := by
    exact Nat.mul_le_mul_left 11
      (Nat.le_mul_of_pos_right (n + 1) (by omega))
  have h3 :
      11 * ((n + 1) * (n + 1)) ≤
        11 * (((n + 1) * (n + 1)) * (n + 1)) := by
    exact Nat.mul_le_mul_left 11
      (Nat.le_mul_of_pos_right ((n + 1) * (n + 1)) (by omega))
  have h4 :
      11 * (((n + 1) * (n + 1)) * (n + 1)) ≤
        8192 * (((n + 1) * (n + 1)) * (n + 1)) :=
    Nat.mul_le_mul_right (((n + 1) * (n + 1)) * (n + 1)) (by omega)
  unfold checkedVerifierExactTimeBound
  simp [Nat.pow_succ, Nat.pow_two, Nat.mul_assoc] at *
  exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))

theorem three_mul_add_ten_le_exact_global (n : Nat) :
    3 * n + 10 ≤ checkedVerifierExactTimeBound n := by
  have h1 : 3 * n + 10 ≤ 10 * (n + 1) := by omega
  have h2 :
      10 * (n + 1) ≤ 10 * ((n + 1) * (n + 1)) := by
    exact Nat.mul_le_mul_left 10
      (Nat.le_mul_of_pos_right (n + 1) (by omega))
  have h3 :
      10 * ((n + 1) * (n + 1)) ≤
        10 * (((n + 1) * (n + 1)) * (n + 1)) := by
    exact Nat.mul_le_mul_left 10
      (Nat.le_mul_of_pos_right ((n + 1) * (n + 1)) (by omega))
  have h4 :
      10 * (((n + 1) * (n + 1)) * (n + 1)) ≤
        8192 * (((n + 1) * (n + 1)) * (n + 1)) :=
    Nat.mul_le_mul_right (((n + 1) * (n + 1)) * (n + 1)) (by omega)
  unfold checkedVerifierExactTimeBound
  simp [Nat.pow_succ, Nat.pow_two, Nat.mul_assoc] at *
  exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))

theorem scan_plus_step_le_exact_global (n : Nat) :
    n + 3 + checkedStepEnvelope n ≤
      checkedVerifierExactTimeBound n := by
  have hlin : n + 3 ≤ 3 * (n + 1) := by omega
  have hlin2 :
      3 * (n + 1) ≤ 3 * ((n + 1) * (n + 1)) := by
    exact Nat.mul_le_mul_left 3
      (Nat.le_mul_of_pos_right (n + 1) (by omega))
  have hsum :
      n + 3 + 128 * ((n + 1) * (n + 1)) ≤
        131 * ((n + 1) * (n + 1)) := by
    omega
  have hcubic :
      131 * ((n + 1) * (n + 1)) ≤
        131 * (((n + 1) * (n + 1)) * (n + 1)) := by
    exact Nat.mul_le_mul_left 131
      (Nat.le_mul_of_pos_right ((n + 1) * (n + 1)) (by omega))
  have hcoef :
      131 * (((n + 1) * (n + 1)) * (n + 1)) ≤
        8192 * (((n + 1) * (n + 1)) * (n + 1)) :=
    Nat.mul_le_mul_right (((n + 1) * (n + 1)) * (n + 1)) (by omega)
  unfold checkedStepEnvelope checkedVerifierExactTimeBound
  simp [Nat.pow_succ, Nat.pow_two, Nat.mul_assoc] at *
  exact Nat.le_trans hsum (Nat.le_trans hcubic hcoef)

/-- Lift any already-established fail-closed fuel to the common exact global
fuel. -/
theorem promote_fail_closed
    (source witness : BitString)
    (t : Nat)
    (ht : t ≤ checkedVerifierExactTimeBound source.length)
    (hhalt :
      checkedVerifierMachine.HaltsWithin t
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source })
    (hnot :
      ¬ checkedVerifierMachine.AcceptsWithin t
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source }) :
    checkedVerifierMachine.HaltsWithin
        (checkedVerifierExactTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierExactTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  let start : VerifierConfig :=
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness source }
  have hh :=
    P01NTMRunLaws.haltsWithin_mono_le
      checkedVerifierMachine t
        (checkedVerifierExactTimeBound source.length)
      start ht (by simpa [start] using hhalt)
  have hn :=
    not_acceptsWithin_mono_after_halt
      t (checkedVerifierExactTimeBound source.length)
      start ht (by simpa [start] using hhalt)
      (by simpa [start] using hnot)
  exact ⟨by simpa [start] using hh, by simpa [start] using hn⟩

/-- Empty raw source rejects in one physical verifier step. -/
theorem prepared_empty_fail_closed_exact
    (witness : BitString) :
    checkedVerifierMachine.HaltsWithin
        (checkedVerifierExactTimeBound 0)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierExactTimeBound 0)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] } := by
  let start : VerifierConfig :=
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness [] }
  let terminal : VerifierConfig :=
    { state := .reject, tape := preparedTape witness [] }
  have hreach :
      terminal ∈ checkedVerifierMachine.runBranches 1 [start] := by
    dsimp [start, terminal]
    simp [NTM.runBranches, NTM.successors, NTM.stepBranch,
      checkedVerifierMachine, preparedTape, P01NTMRunLaws.Halted,
      Tape.write, Tape.move]
  have hhaltTerminal : P01NTMRunLaws.Halted checkedVerifierMachine terminal := by
    simp [terminal, P01NTMRunLaws.Halted, checkedVerifierMachine]
  have hhalt1 :
      checkedVerifierMachine.HaltsWithin 1 start :=
    P01CheckedVerifierDeterminism.haltsWithin_of_reaches_halted 1 start terminal hreach hhaltTerminal
  have hnot1 :
      ¬ checkedVerifierMachine.AcceptsWithin 1 start := by
    intro h
    rcases h with ⟨z, hz, hacc⟩
    have heq :=
      P01CheckedVerifierDeterminism.runBranches_eq_singleton_of_mem
        1 start terminal hreach
    rw [heq] at hz
    simp only [List.mem_singleton] at hz
    subst z
    simp [terminal, checkedVerifierMachine] at hacc
  have hle : 1 ≤ checkedVerifierExactTimeBound 0 := by
    decide
  exact promote_fail_closed [] witness 1 hle
    (by simpa [start] using hhalt1)
    (by simpa [start] using hnot1)

/-- Nonempty source shorter than one full tag is fail-closed at exact global
fuel. -/
theorem prepared_truncated_tag_fail_closed_exact
    (witness source : BitString)
    (hne : source ≠ [])
    (hshort : source.length < 3) :
    checkedVerifierMachine.HaltsWithin
        (checkedVerifierExactTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierExactTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  obtain ⟨t, ht, hh, hn⟩ :=
    P01RawMalformedTag.prepared_truncated_tag_fail_closed
      witness source hne hshort
  exact promote_fail_closed source witness t
    (Nat.le_trans ht (two_mul_add_eleven_le_exact_global source.length))
    hh hn

/-- decodeNat can fail only by exhausting a string of ones. -/
theorem decodeNat_none_eq_replicate_true
    (bits : BitString)
    (h : decodeNat bits = none) :
    bits = List.replicate bits.length true := by
  rcases P01RawDecodeFailureDescent.decodeNat_none_replicate_true bits h with
    ⟨k, hk⟩
  subst bits
  simp

/-- A malformed unary input payload is fail-closed at exact global fuel. -/
theorem prepared_input_unary_none_fail_closed_exact
    (witness rest : BitString)
    (h : decodeNat rest = none) :
    let source : BitString := false :: false :: false :: rest
    checkedVerifierMachine.HaltsWithin
        (checkedVerifierExactTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierExactTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  have hrest := decodeNat_none_eq_replicate_true rest h
  let source : BitString := false :: false :: false :: rest
  obtain ⟨t, ht, hh, hn⟩ :=
    P01RawMalformedUnary.prepared_truncated_unary_fail_closed
      witness rest.length
  have hsrc :
      (false :: false :: false :: List.replicate rest.length true : BitString) =
        source := by
    simp [source, ← hrest]
  rw [hsrc] at ht hh hn
  exact promote_fail_closed source witness t
    (Nat.le_trans ht (three_mul_add_ten_le_exact_global source.length))
    hh hn

/-- If the checked evaluator reaches physical reject from its root on a
nonempty source within one common step envelope, the full verifier is
fail-closed at exact global fuel. -/
theorem prepared_eval_reject_within_step_fail_closed_exact
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (m : Nat) (tape : Tape (Option Bool))
    (hm : m ≤ checkedStepEnvelope (b :: bs).length)
    (hreach :
      ({ state := .reject, tape := tape } : EvalConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := checkedEvalRunLoopMachine.initial,
             tape := P01EvalCursorMachine.evalCursorStackEndTape
               witness 0 (b :: bs) [] 0 }]) :
    checkedVerifierMachine.HaltsWithin
        (checkedVerifierExactTimeBound (b :: bs).length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierExactTimeBound (b :: bs).length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } := by
  obtain ⟨m0, hm0, hfull⟩ :=
    prepared_nonempty_lift_eval_reach
      witness b bs m
      ({ state := .reject, tape := tape } : EvalConfig)
      hreach
  let start : VerifierConfig :=
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness (b :: bs) }
  let terminal : VerifierConfig :=
    { state := .reject, tape := tape }
  have hreachV :
      terminal ∈ checkedVerifierMachine.runBranches (m0 + m) [start] := by
    simpa [start, terminal, P01NTMRunLaws.liftConfig,
      P01CheckedVerifierCompositeNTM.checkedEvalEmbed] using hfull
  have hhaltTerminal : P01NTMRunLaws.Halted checkedVerifierMachine terminal := by
    simp [terminal, P01NTMRunLaws.Halted, checkedVerifierMachine]
  have hh :
      checkedVerifierMachine.HaltsWithin (m0 + m) start :=
    P01CheckedVerifierDeterminism.haltsWithin_of_reaches_halted (m0 + m) start terminal
      hreachV hhaltTerminal
  have hn :
      ¬ checkedVerifierMachine.AcceptsWithin (m0 + m) start := by
    intro hacc
    rcases hacc with ⟨z, hz, hzacc⟩
    have heq :=
      P01CheckedVerifierDeterminism.runBranches_eq_singleton_of_mem
        (m0 + m) start terminal hreachV
    rw [heq] at hz
    simp only [List.mem_singleton] at hz
    subst z
    simp [terminal, checkedVerifierMachine] at hzacc
  have htotal :
      m0 + m ≤ checkedVerifierExactTimeBound (b :: bs).length := by
    have hraw :
        m0 + m ≤ (b :: bs).length + 3 +
          checkedStepEnvelope (b :: bs).length := by
      omega
    exact Nat.le_trans hraw
      (scan_plus_step_le_exact_global (b :: bs).length)
  exact promote_fail_closed (b :: bs) witness (m0 + m) htotal
    (by simpa [start] using hh)
    (by simpa [start] using hn)

/-- Invalid raw tags 110 and 111 are fail-closed at exact global fuel. -/
theorem prepared_invalid_terminal_tag_fail_closed_exact
    (witness rest : BitString)
    (b2 : Bool) :
    let source : BitString := true :: true :: b2 :: rest
    checkedVerifierMachine.HaltsWithin
        (checkedVerifierExactTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierExactTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  let source : BitString := true :: true :: b2 :: rest
  have hdis :
      P01CNFMode.tagAllowed .cnf
        (P01NeedExprTagDecode.decodeTagBits true true b2) = false := by
    cases b2 <;> rfl
  obtain ⟨m, hm, hreach⟩ :=
    disallowed_tag_prefix_reaches_reject
      .cnf witness rest [] 0 0 true true b2 hdis
  have hm' : m ≤ checkedStepEnvelope source.length := by
    exact Nat.le_trans hm
      (checkedTagPrefixFuel_le_envelope source.length source []
        (Nat.le_refl _) (by simp))
  have hreach' :
      ({ state := .reject,
         tape :=
           P01EvalCursorMachine.evalCursorReadTape witness 3 rest [] 0 } :
        EvalConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := checkedEvalRunLoopMachine.initial,
             tape :=
               P01EvalCursorMachine.evalCursorStackEndTape
                 witness 0 source [] 0 }] := by
    simpa [source, checkedEvalRunLoopMachine] using hreach
  simpa [source] using
    (prepared_eval_reject_within_step_fail_closed_exact
      witness true (true :: b2 :: rest) m
      (P01EvalCursorMachine.evalCursorReadTape witness 3 rest [] 0)
      (by simpa [source] using hm')
      (by simpa [source] using hreach'))

#print axioms MCore.Real.P01RawBaseExact.prepared_empty_fail_closed_exact
#print axioms MCore.Real.P01RawBaseExact.prepared_truncated_tag_fail_closed_exact
#print axioms MCore.Real.P01RawBaseExact.decodeNat_none_eq_replicate_true
#print axioms MCore.Real.P01RawBaseExact.prepared_input_unary_none_fail_closed_exact
#print axioms MCore.Real.P01RawBaseExact.prepared_invalid_terminal_tag_fail_closed_exact

end P01RawBaseExact
end Real
end MCore
