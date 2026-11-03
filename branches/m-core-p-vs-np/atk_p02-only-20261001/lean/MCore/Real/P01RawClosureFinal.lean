import MCore.Real.P01RawCoreFailureRecursive
import MCore.Real.P01RawResidualReject
import MCore.Real.P01RawVerifierLift
import MCore.Real.P01RawDeadEnd
import MCore.Real.P01RawSourceSplit
import MCore.Real.P01ExactBoundedReject
import MCore.Real.P01ExactVerifierCanonicalRun
import MCore.Real.P01ExactVerifierGlobalBudget
import MCore.Real.P01CheckedVerifierFiniteState
import MCore.Real.P01DirectVerifierInhabitant
import MCore.Real.P01WitnessPrepGlobal

namespace MCore
namespace Real
namespace P01RawClosureFinal

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01GuessedWitnessRelation
open P01CNFMode
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierInvariant
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierDeterminism
open P01CheckedVerifierFiniteState
open P01CheckedEvalRunBoundedCertificate
open P01ExactBoundedReject
open P01ExactVerifierCanonicalRun
open P01ExactVerifierGlobalBudget
open P01RawCoreFailure
open P01RawCoreFailureRecursive
open P01RawResidualReject
open P01RawVerifierLift
open P01RawDeadEnd
open P01RawSourceSplit
open P01DirectVerifierInhabitant
open P01WitnessPreservingPrep
open P01WitnessPrepGlobal
open P01IntegratedAssembly
open P01NTMRunLaws

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

abbrev VerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

/-- One common cubic clock for both canonical and malformed raw sources.
The larger constant only absorbs the fail-closed recursive raw-source path. -/
def unifiedVerifierTimeBound : TimeBound :=
  fun n => 65536 * (n + 1) ^ 3

theorem unifiedVerifierTimeBound_poly :
    PolynomialTimeBound unifiedVerifierTimeBound := by
  refine ⟨65536, 3, ?_⟩
  intro n
  exact Nat.le_refl _

theorem exactTime_le_unified (n : Nat) :
    checkedVerifierExactTimeBound n ≤ unifiedVerifierTimeBound n := by
  unfold checkedVerifierExactTimeBound unifiedVerifierTimeBound
  exact Nat.mul_le_mul_right ((n + 1) ^ 3) (by omega)

private theorem linear_four_le_cubic (n : Nat) :
    n + 4 ≤ 4 * (n + 1) ^ 3 := by
  have h0 : n + 4 ≤ 4 * (n + 1) := by omega
  have h1 : n + 1 ≤ (n + 1) ^ 2 := by
    have hp : 1 ≤ n + 1 := by omega
    calc
      n + 1 = (n + 1) * 1 := by simp
      _ ≤ (n + 1) * (n + 1) :=
        Nat.mul_le_mul_left (n + 1) hp
      _ = (n + 1) ^ 2 := by ring
  have h2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := by
    have hp : 1 ≤ n + 1 := by omega
    calc
      (n + 1) ^ 2 = (n + 1) ^ 2 * 1 := by simp
      _ ≤ (n + 1) ^ 2 * (n + 1) :=
        Nat.mul_le_mul_left ((n + 1) ^ 2) hp
      _ = (n + 1) ^ 3 := by ring
  exact Nat.le_trans h0
    (Nat.le_trans
      (Nat.mul_le_mul_left 4 h1)
      (Nat.mul_le_mul_left 4 h2))

private theorem linear_seven_le_cubic (n : Nat) :
    n + 7 ≤ 7 * (n + 1) ^ 3 := by
  have h0 : n + 7 ≤ 7 * (n + 1) := by omega
  have h1 : n + 1 ≤ (n + 1) ^ 2 := by
    have hp : 1 ≤ n + 1 := by omega
    calc
      n + 1 = (n + 1) * 1 := by simp
      _ ≤ (n + 1) * (n + 1) :=
        Nat.mul_le_mul_left (n + 1) hp
      _ = (n + 1) ^ 2 := by ring
  have h2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := by
    have hp : 1 ≤ n + 1 := by omega
    calc
      (n + 1) ^ 2 = (n + 1) ^ 2 * 1 := by simp
      _ ≤ (n + 1) ^ 2 * (n + 1) :=
        Nat.mul_le_mul_left ((n + 1) ^ 2) hp
      _ = (n + 1) ^ 3 := by ring
  exact Nat.le_trans h0
    (Nat.le_trans
      (Nat.mul_le_mul_left 7 h1)
      (Nat.mul_le_mul_left 7 h2))

theorem rawCoreBudget_root_eq (n : Nat) :
    rawCoreBudget n n = 16384 * (n + 1) ^ 3 := by
  unfold rawCoreBudget P01CheckedVerifierGlobalBudget.checkedLoopStepEnvelope
  ring

theorem rawCore_with_wrapper_le_unified
    (n m : Nat)
    (hm : m ≤ rawCoreBudget n n) :
    n + 3 + m + 1 ≤ unifiedVerifierTimeBound n := by
  have hr : m ≤ 16384 * (n + 1) ^ 3 := by
    simpa [rawCoreBudget_root_eq n] using hm
  have hl := linear_four_le_cubic n
  unfold unifiedVerifierTimeBound
  omega

theorem circuit_with_wrapper_le_unified
    (n m : Nat) (phi : Circuit)
    (henc : (encodeCircuit phi).length ≤ n)
    (hm : m ≤ checkedCircuitBudget phi n + 3) :
    n + 3 + m + 1 ≤ unifiedVerifierTimeBound n := by
  have hc := checkedCircuitBudget_le_exact_global n phi henc
  have hl := linear_seven_le_cubic n
  unfold unifiedVerifierTimeBound
  omega

/-- Once a verifier has halted, acceptance at any larger fuel is equivalent to
acceptance at the halting fuel. -/
theorem acceptsWithin_iff_larger_of_halts
    (n m : Nat) (start : VerifierConfig)
    (hnm : n ≤ m)
    (hhalt : checkedVerifierMachine.HaltsWithin n start) :
    checkedVerifierMachine.AcceptsWithin m start ↔
      checkedVerifierMachine.AcceptsWithin n start := by
  constructor
  · rintro ⟨z, hz, hacc⟩
    have hzh : Halted checkedVerifierMachine z :=
      halted_of_accepting checkedVerifierMachine z hacc
    exact ⟨z,
      mem_of_haltsWithin checkedVerifierMachine n m start z
        hhalt hz hzh,
      hacc⟩
  · rintro ⟨z, hz, hacc⟩
    have hzh : Halted checkedVerifierMachine z :=
      halted_of_accepting checkedVerifierMachine z hacc
    have hp :=
      mem_runBranches_persist checkedVerifierMachine
        n (m - n) [start] z hz hzh
    have heq : n + (m - n) = m := by omega
    exact ⟨z, by simpa [heq] using hp, hacc⟩

/-- Lift either form of evaluator fail-closed endpoint to the prepared verifier.
Explicit reject is already halted; an active dead state is discharged by the
generic dead-end theorem. -/
theorem prepared_nonempty_raw_fail_closed
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (m : Nat) (target : EvalConfig)
    (hreach :
      target ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := checkedEvalRunLoopMachine.initial,
           tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }])
    (hend : RawFailEndpoint target) :
    ∃ total ≤ (b :: bs).length + 3 + m + 1,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } := by
  rcases hend with hreject | hdead
  · obtain ⟨m0, hm0, hfull⟩ :=
      prepared_nonempty_lift_eval_reach
        witness b bs m target hreach
    let start : VerifierConfig :=
      { state := checkedVerifierMachine.initial,
        tape := preparedTape witness (b :: bs) }
    let lifted : VerifierConfig :=
      liftConfig checkedEvalEmbed target
    have hfull' :
        lifted ∈ checkedVerifierMachine.runBranches (m0 + m) [start] := by
      simpa [start, lifted] using hfull
    have hhalted : Halted checkedVerifierMachine lifted := by
      rcases target with ⟨q, tape⟩
      simp only at hreject
      subst q
      simp [lifted, liftConfig, checkedEvalEmbed, Halted,
        checkedVerifierMachine, checkedEvalRunLoopMachine]
    have hhalt :
        checkedVerifierMachine.HaltsWithin (m0 + m) start :=
      haltsWithin_of_reaches_halted (m0 + m) start lifted hfull' hhalted
    have hnot :
        ¬ checkedVerifierMachine.AcceptsWithin (m0 + m) start := by
      rw [acceptsWithin_iff_of_reached_terminal
        (m0 + m) start lifted hfull']
      rcases target with ⟨q, tape⟩
      simp only at hreject
      subst q
      simp [lifted, liftConfig, checkedEvalEmbed, checkedVerifierMachine]
    refine ⟨m0 + m, ?_, hhalt, hnot⟩
    omega
  · exact
      prepared_nonempty_dead_fail_closed
        witness b bs m target hreach hdead.1 hdead.2

/-- Every recursive core-decoder failure on a nonempty source is globally
fail-closed at the prepared-verifier level, within the common cubic clock. -/
theorem core_none_nonempty_fail_closed
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (hw : witness.length = (b :: bs).length)
    (hcore :
      decodeCircuitCore ((b :: bs).length + 1) (b :: bs) = none) :
    checkedVerifierMachine.HaltsWithin
        (unifiedVerifierTimeBound (b :: bs).length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (unifiedVerifierTimeBound (b :: bs).length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } := by
  let n := (b :: bs).length
  have hfuel : (b :: bs).length < 3 * ((b :: bs).length + 1) := by
    omega
  have hLayout :
      CheckedLayoutBound n 0 (b :: bs) (encodeEvalFrames []) := by
    simpa [n] using (CheckedLayoutBound.root (b :: bs))
  obtain ⟨m, hm, cfg, hreach, hend⟩ :=
    decodeCore_none_reaches_raw_failure
      ((b :: bs).length + 1) (b :: bs) hfuel
      n .cnf witness [] 0 0
      (by simpa [n] using hw) hLayout hcore
  have hreach' :
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := checkedEvalRunLoopMachine.initial,
           tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }] := by
    simpa [checkedEvalRunLoopMachine] using hreach
  obtain ⟨total, htotal, hhalt, hnot⟩ :=
    prepared_nonempty_raw_fail_closed witness b bs m cfg hreach' hend
  have hTU :
      total ≤ unifiedVerifierTimeBound (b :: bs).length :=
    Nat.le_trans htotal
      (rawCore_with_wrapper_le_unified (b :: bs).length m (by
        simpa [n] using hm))
  constructor
  · exact haltsWithin_mono_le checkedVerifierMachine
      total (unifiedVerifierTimeBound (b :: bs).length)
      { state := checkedVerifierMachine.initial,
        tape := preparedTape witness (b :: bs) }
      hTU hhalt
  · exact not_acceptsWithin_mono_after_halt
      total (unifiedVerifierTimeBound (b :: bs).length)
      { state := checkedVerifierMachine.initial,
        tape := preparedTape witness (b :: bs) }
      hTU hhalt hnot

/-- Decoder success with a nonempty residual tail is also fail-closed.
If the decoded prefix is CNF, evaluate it and reject the leftover source;
otherwise reject structurally inside the bounded evaluator. -/
theorem residual_nonempty_fail_closed
    (witness source : BitString)
    (phi : Circuit) (tb : Bool) (tail : BitString)
    (hw : witness.length = source.length)
    (hcore :
      decodeCircuitCore (source.length + 1) source =
        some (phi, tb :: tail)) :
    checkedVerifierMachine.HaltsWithin
        (unifiedVerifierTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (unifiedVerifierTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  have hsource :
      source = encodeCircuit phi ++ (tb :: tail) :=
    P01GuessedWitnessRelation.decodeCircuitCore_sound
      (source.length + 1) source phi (tb :: tail) hcore
  have henc : (encodeCircuit phi).length ≤ source.length := by
    rw [hsource]
    simp
  have hlen : varBound phi ≤ witness.length := by
    rw [hw]
    exact Nat.le_trans (varBound_le_encoded_length phi) henc
  let sigma : Assignment := fun i => witness.getD i false
  have hread :
      ∀ i, i < varBound phi →
        witness.getD i false = sigma i := by
    intro i hi
    rfl
  have hLayout :
      CheckedLayoutBound source.length 0
        (encodeCircuit phi ++ (tb :: tail))
        (encodeEvalFrames []) := by
    simpa [hsource] using (CheckedLayoutBound.root source)
  cases hmode : modeCheck .cnf phi with
  | true =>
      obtain ⟨m, hm, cfg, hreach, hreject⟩ :=
        canonical_prefix_with_residual_reaches_reject
          sigma witness phi (tb :: tail) (by simp)
          hmode source.length hLayout hlen hread
      have hreach' :
          cfg ∈ checkedEvalRunLoopMachine.runBranches m
            [{ state := checkedEvalRunLoopMachine.initial,
               tape := evalCursorStackEndTape witness 0 source [] 0 }] := by
        simpa [hsource, checkedEvalRunLoopMachine] using hreach
      have hend : RawFailEndpoint cfg := Or.inl hreject
      cases hs : source with
      | nil =>
          simp [hs] at hsource
      | cons b bs =>
          obtain ⟨total, htotal, hhalt, hnot⟩ :=
            prepared_nonempty_raw_fail_closed
              witness b bs m cfg (by simpa [hs] using hreach') hend
          have hm' :
              m ≤ checkedCircuitBudget phi source.length + 3 := hm
          have hbudget :
              total ≤ unifiedVerifierTimeBound source.length :=
            Nat.le_trans (by simpa [hs] using htotal)
              (circuit_with_wrapper_le_unified
                source.length m phi henc hm')
          constructor
          · exact haltsWithin_mono_le checkedVerifierMachine
              total (unifiedVerifierTimeBound source.length)
              { state := checkedVerifierMachine.initial,
                tape := preparedTape witness source }
              hbudget (by simpa [hs] using hhalt)
          · exact not_acceptsWithin_mono_after_halt
              total (unifiedVerifierTimeBound source.length)
              { state := checkedVerifierMachine.initial,
                tape := preparedTape witness source }
              hbudget (by simpa [hs] using hhalt)
              (by simpa [hs] using hnot)
  | false =>
      obtain ⟨m, hm, cfg, hreach, hreject⟩ :=
        (circuit_exact_bounded_reject sigma witness phi .cnf)
          hmode (tb :: tail) [] 0 0 source.length
          hLayout hlen hread
      have hreach' :
          cfg ∈ checkedEvalRunLoopMachine.runBranches m
            [{ state := checkedEvalRunLoopMachine.initial,
               tape := evalCursorStackEndTape witness 0 source [] 0 }] := by
        simpa [hsource, checkedEvalRunLoopMachine] using hreach
      have hend : RawFailEndpoint cfg := Or.inl hreject
      cases hs : source with
      | nil =>
          simp [hs] at hsource
      | cons b bs =>
          obtain ⟨total, htotal, hhalt, hnot⟩ :=
            prepared_nonempty_raw_fail_closed
              witness b bs m cfg (by simpa [hs] using hreach') hend
          have hm' :
              m ≤ checkedCircuitBudget phi source.length + 3 :=
            Nat.le_trans hm (Nat.le_add_right _ _)
          have hbudget :
              total ≤ unifiedVerifierTimeBound source.length :=
            Nat.le_trans (by simpa [hs] using htotal)
              (circuit_with_wrapper_le_unified
                source.length m phi henc hm')
          constructor
          · exact haltsWithin_mono_le checkedVerifierMachine
              total (unifiedVerifierTimeBound source.length)
              { state := checkedVerifierMachine.initial,
                tape := preparedTape witness source }
              hbudget (by simpa [hs] using hhalt)
          · exact not_acceptsWithin_mono_after_halt
              total (unifiedVerifierTimeBound source.length)
              { state := checkedVerifierMachine.initial,
                tape := preparedTape witness source }
              hbudget (by simpa [hs] using hhalt)
              (by simpa [hs] using hnot)

/-- Every whole-source decoder failure is physically fail-closed at the single
unified cubic fuel. -/
theorem malformed_source_fail_closed
    (source witness : BitString)
    (hw : witness.length = source.length)
    (hdecode : decodeCircuit source = none) :
    checkedVerifierMachine.HaltsWithin
        (unifiedVerifierTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (unifiedVerifierTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  cases hs : source with
  | nil =>
      let start : VerifierConfig :=
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] }
      let terminal : VerifierConfig :=
        { state := .reject, tape := preparedTape witness [] }
      have hreach :
          terminal ∈ checkedVerifierMachine.runBranches 1 [start] := by
        dsimp [start, terminal]
        simp [preparedTape, checkedVerifierMachine,
          NTM.runBranches, NTM.successors, NTM.stepBranch,
          Halted, Tape.write, Tape.move]
      have hhalted : Halted checkedVerifierMachine terminal := by
        simp [terminal, Halted, checkedVerifierMachine]
      have hhalt1 :
          checkedVerifierMachine.HaltsWithin 1 start :=
        haltsWithin_of_reaches_halted 1 start terminal hreach hhalted
      have hnot1 :
          ¬ checkedVerifierMachine.AcceptsWithin 1 start := by
        rw [acceptsWithin_iff_of_reached_terminal 1 start terminal hreach]
        simp [terminal, checkedVerifierMachine]
      have hle : 1 ≤ unifiedVerifierTimeBound 0 := by
        simp [unifiedVerifierTimeBound]
      constructor
      · simpa [hs, start] using
          haltsWithin_mono_le checkedVerifierMachine
            1 (unifiedVerifierTimeBound 0) start hle hhalt1
      · simpa [hs, start] using
          not_acceptsWithin_mono_after_halt
            1 (unifiedVerifierTimeBound 0) start hle hhalt1 hnot1
  | cons b bs =>
      cases hc :
          decodeCircuitCore ((b :: bs).length + 1) (b :: bs) with
      | none =>
          exact core_none_nonempty_fail_closed witness b bs
            (by simpa [hs] using hw) hc
      | some p =>
          rcases p with ⟨phi, tail0⟩
          cases ht : tail0 with
          | nil =>
              unfold decodeCircuit at hdecode
              simp [hc, ht] at hdecode
          | cons tb tail =>
              exact residual_nonempty_fail_closed
                witness (b :: bs) phi tb tail
                (by simpa [hs] using hw)
                (by simpa [ht] using hc)

/-- Canonical sources remain correct when the exact 8192-cubic clock is
increased to the unified clock. -/
theorem canonical_source_at_unified
    (witness : BitString) (phi : Circuit)
    (hlen : varBound phi ≤ witness.length) :
    checkedVerifierMachine.HaltsWithin
        (unifiedVerifierTimeBound (encodeCircuit phi).length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (encodeCircuit phi) } ∧
      (checkedVerifierMachine.AcceptsWithin
          (unifiedVerifierTimeBound (encodeCircuit phi).length)
          { state := checkedVerifierMachine.initial,
            tape := preparedTape witness (encodeCircuit phi) } ↔
        VerifyBits (encodeCircuit phi) witness) := by
  let T0 := checkedVerifierExactTimeBound (encodeCircuit phi).length
  let T := unifiedVerifierTimeBound (encodeCircuit phi).length
  let start : VerifierConfig :=
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness (encodeCircuit phi) }
  have hhalt0 :
      checkedVerifierMachine.HaltsWithin T0 start := by
    simpa [T0, start] using
      prepared_canonical_halts_within_exact_global witness phi hlen
  have hcorr0 :
      checkedVerifierMachine.AcceptsWithin T0 start ↔
        VerifyBits (encodeCircuit phi) witness := by
    simpa [T0, start] using
      prepared_canonical_accepts_iff_exact_global witness phi hlen
  have hle : T0 ≤ T := by
    simpa [T0, T] using exactTime_le_unified (encodeCircuit phi).length
  constructor
  · exact haltsWithin_mono_le checkedVerifierMachine T0 T start hle hhalt0
  · exact (acceptsWithin_iff_larger_of_halts T0 T start hle hhalt0).trans hcorr0

/-- Total physical verifier semantics for every raw bitstring at one polynomial
clock. -/
theorem checked_total_unified
    (source witness : BitString)
    (hw : witness.length = source.length) :
    checkedVerifierMachine.HaltsWithin
        (unifiedVerifierTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      (checkedVerifierMachine.AcceptsWithin
          (unifiedVerifierTimeBound source.length)
          { state := checkedVerifierMachine.initial,
            tape := preparedTape witness source } ↔
        VerifyBits source witness) := by
  rcases exact_encoding_or_decode_none source with hcanon | hraw
  · rcases hcanon with ⟨phi, rfl⟩
    have hlen : varBound phi ≤ witness.length := by
      rw [hw]
      exact varBound_le_encoded_length phi
    exact canonical_source_at_unified witness phi hlen
  · have hfail := malformed_source_fail_closed source witness hw hraw
    constructor
    · exact hfail.1
    · constructor
      · intro hacc
        exact False.elim (hfail.2 hacc)
      · intro hver
        exact False.elim ((verifyBits_false_of_decode_none source witness hraw) hver)

/-- The concrete checked verifier packaged as the exact remaining verifier
phase for the already-closed witness-preparation phase. -/
noncomputable def unifiedVerifierPhase :
    P01VerifierPhase prepPhase.layout where
  stateCount := checkedVerifierStateCount
  machine := checkedVerifierFinMachine
  blank_none := checkedVerifierFinMachine_blank
  timeBound := unifiedVerifierTimeBound
  time_poly := unifiedVerifierTimeBound_poly
  halts := by
    intro bs w hw
    have h := (checked_total_unified bs w hw).1
    have hfin :=
      (checkedVerifierFinMachine_haltsWithin_iff
        (unifiedVerifierTimeBound bs.length)
        ({ state := checkedVerifierMachine.initial,
           tape := preparedTape w bs } : VerifierConfig)).2 h
    change checkedVerifierFinMachine.HaltsWithin
      (unifiedVerifierTimeBound bs.length)
      (liftConfig checkedVerifierStateEncode
        ({ state := checkedVerifierMachine.initial,
           tape := preparedTape w bs } : VerifierConfig))
    exact hfin
  correct := by
    intro bs w hw
    have h := (checked_total_unified bs w hw).2
    have hfin :=
      checkedVerifierFinMachine_acceptsWithin_iff
        (unifiedVerifierTimeBound bs.length)
        ({ state := checkedVerifierMachine.initial,
           tape := preparedTape w bs } : VerifierConfig)
    change
      (checkedVerifierFinMachine.AcceptsWithin
          (unifiedVerifierTimeBound bs.length)
          (liftConfig checkedVerifierStateEncode
            ({ state := checkedVerifierMachine.initial,
               tape := preparedTape w bs } : VerifierConfig)) ↔
        VerifyBits bs w)
    exact hfin.trans h

/-- No-hypothesis inhabitant of the exact P01 construction gap. -/
theorem p01ConstructionGap_closed :
    P01FinalCertificate.P01ConstructionGap :=
  p01_of_verifier unifiedVerifierPhase

#print axioms MCore.Real.P01RawClosureFinal.unifiedVerifierTimeBound_poly
#print axioms MCore.Real.P01RawClosureFinal.malformed_source_fail_closed
#print axioms MCore.Real.P01RawClosureFinal.checked_total_unified
#print axioms MCore.Real.P01RawClosureFinal.unifiedVerifierPhase
#print axioms MCore.Real.P01RawClosureFinal.p01ConstructionGap_closed

-- ATK final closure rerun trigger 2026-10-01; no semantic change.
-- ATK certificate sync 2026-10-01; no semantic change.
end P01RawClosureFinal
end Real
end MCore
