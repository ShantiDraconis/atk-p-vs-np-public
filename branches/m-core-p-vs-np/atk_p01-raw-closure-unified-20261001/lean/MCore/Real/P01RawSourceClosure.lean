import MCore.Real.P01RawCoreFailureRecursive
import MCore.Real.P01RawResidualReject
import MCore.Real.P01CheckedVerifierFiniteState
import MCore.Real.P01WitnessPrepGlobal
import MCore.Real.P01IntegratedAssembly
import MCore.Real.P01DirectVerifierInhabitant
import MCore.Real.P01ExactVerifierCanonicalRun
import MCore.Real.P01ExactVerifierGlobalBudget

namespace MCore
namespace Real
namespace P01RawSourceClosure

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01GuessedWitnessRelation
open P01IntegratedAssembly
open P01WitnessPrepGlobal
open P01WitnessPreservingPrep
open P01EvalCursorMachine
open P01EncodedStackEvaluator
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierRun
open P01CheckedVerifierDeterminism
open P01CheckedVerifierFiniteState
open P01ExactVerifierCanonicalRun
open P01ExactVerifierGlobalBudget
open P01ExactBoundedCircuitProducer
open P01ExactBoundedReject
open P01RawResidualReject
open P01RawVerifierLift
open P01RawDeadEnd
open P01RawCoreFailure
open P01RawCoreFailureRecursive
open P01NTMRunLaws
open P01CNFMode

abbrev VerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- One uniform cubic budget covering both canonical exact execution and every
raw fail-closed path.  It is deliberately loose; only polynomiality matters. -/
def rawVerifierTimeBound : TimeBound :=
  fun n => 65536 * (n + 1) ^ 3

theorem rawVerifierTimeBound_poly :
    PolynomialTimeBound rawVerifierTimeBound := by
  exact ⟨65536, 3, fun n => Nat.le_refl _⟩

theorem exactTimeBound_le_raw
    (n : Nat) :
    checkedVerifierExactTimeBound n ≤ rawVerifierTimeBound n := by
  unfold checkedVerifierExactTimeBound rawVerifierTimeBound
  exact Nat.mul_le_mul_right ((n + 1) ^ 3) (by omega)

theorem linear_le_cube_budget
    (n : Nat) :
    n + 7 ≤ 7 * (n + 1) ^ 3 := by
  have hpos : 0 < n + 1 := by omega
  have h1 : n + 1 ≤ (n + 1) * (n + 1) :=
    Nat.le_mul_of_pos_right (n + 1) hpos
  have h2 :
      (n + 1) * (n + 1) ≤
        (n + 1) * (n + 1) * (n + 1) :=
    Nat.le_mul_of_pos_right ((n + 1) * (n + 1)) hpos
  have hc : n + 1 ≤ (n + 1) ^ 3 := by
    calc
      n + 1 ≤ (n + 1) * (n + 1) := h1
      _ ≤ (n + 1) * (n + 1) * (n + 1) := h2
      _ = (n + 1) ^ 3 := by ring
  omega

theorem root_rawCoreBudget_le
    (n : Nat) :
    rawCoreBudget n n ≤ 16384 * (n + 1) ^ 3 := by
  unfold rawCoreBudget checkedLoopStepEnvelope
  ring_nf
  rfl

/-- Empty prepared source is rejected by the verifier's start state in one
physical transition. -/
theorem prepared_empty_fail_closed
    (witness : BitString) :
    checkedVerifierMachine.HaltsWithin 1
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] } ∧
      ¬ checkedVerifierMachine.AcceptsWithin 1
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] } := by
  constructor
  · unfold NTM.HaltsWithin
    simp [checkedVerifierMachine, preparedTape, NTM.runBranches,
      NTM.successors, NTM.stepBranch, Halted, Tape.write, Tape.move]
  · intro h
    rcases h with ⟨z, hz, hacc⟩
    simp [checkedVerifierMachine, preparedTape, NTM.runBranches,
      NTM.successors, NTM.stepBranch, Halted, Tape.write, Tape.move] at hz
    rcases hz with rfl
    simp [checkedVerifierMachine] at hacc

/-- Lift one checked-evaluator reject/dead endpoint through the prepared-tape
scanner into a verifier-level fail-closed run. -/
theorem lift_eval_raw_failure
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (m : Nat) (cfg : EvalConfig)
    (hreach :
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := checkedEvalRunLoopMachine.initial,
           tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }])
    (hend : RawFailEndpoint cfg) :
    ∃ total ≤ (b :: bs).length + 3 + m + 1,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } := by
  obtain ⟨m0, hm0, hfull⟩ :=
    prepared_nonempty_lift_eval_reach witness b bs m cfg hreach
  let start : VerifierConfig :=
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness (b :: bs) }
  let lifted : VerifierConfig := liftConfig checkedEvalEmbed cfg
  have hfull' :
      lifted ∈ checkedVerifierMachine.runBranches (m0 + m) [start] := by
    simpa [start, lifted] using hfull
  rcases hend with hreject | hdead
  · rcases cfg with ⟨q, tape⟩
    change q = .reject at hreject
    subst q
    have hlift :
        lifted = ({ state := .reject, tape := tape } : VerifierConfig) := by
      rfl
    have hhalted :
        Halted checkedVerifierMachine lifted := by
      rw [hlift]
      simp [Halted, checkedVerifierMachine]
    have hhalt :
        checkedVerifierMachine.HaltsWithin (m0 + m) start :=
      haltsWithin_of_reaches_halted (m0 + m)
        start lifted hfull' hhalted
    have hnot :
        ¬ checkedVerifierMachine.AcceptsWithin (m0 + m) start := by
      intro hacc
      rcases hacc with ⟨z, hz, hzacc⟩
      have heq :=
        runBranches_eq_singleton_of_mem (m0 + m) start lifted hfull'
      rw [heq] at hz
      have hzEq : z = lifted := by simpa using hz
      subst z
      rw [hlift] at hzacc
      simp [checkedVerifierMachine] at hzacc
    refine ⟨m0 + m, ?_, hhalt, hnot⟩
    omega
  · have hVdead :=
      lifted_eval_dead_is_verifier_dead cfg hdead.1 hdead.2
    have hhalt :=
      haltsWithin_succ_of_reaches_dead
        (m0 + m) start lifted hfull' hVdead.1 hVdead.2
    have hnot :=
      not_acceptsWithin_succ_of_reaches_dead
        (m0 + m) start lifted hfull' hVdead.1 hVdead.2
    refine ⟨m0 + m + 1, ?_, hhalt, hnot⟩
    omega

/-- Decoder-core failure at root is fail-closed within the global raw budget. -/
theorem prepared_core_none_fail_closed
    (source witness : BitString)
    (hw : witness.length = source.length)
    (hcore :
      decodeCircuitCore (source.length + 1) source = none) :
    ∃ total ≤ rawVerifierTimeBound source.length,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  cases source with
  | nil =>
      have h := prepared_empty_fail_closed witness
      refine ⟨1, ?_, h.1, h.2⟩
      unfold rawVerifierTimeBound
      norm_num
  | cons b bs =>
      let n := (b :: bs).length
      have hLayout :
          CheckedLayoutBound n 0 (b :: bs)
            (encodeEvalFrames []) := by
        constructor <;> simp [n]
      have hfuel :
          (b :: bs).length < 3 * ((b :: bs).length + 1) := by
        omega
      obtain ⟨m, hm, cfg, hreach, hend⟩ :=
        decodeCore_none_reaches_raw_failure
          ((b :: bs).length + 1) (b :: bs) hfuel
          n .cnf witness [] 0 0
          (by simpa [n] using hw)
          hLayout hcore
      obtain ⟨total, htotal, hhalt, hnot⟩ :=
        lift_eval_raw_failure witness b bs m cfg
          (by simpa using hreach) hend
      have hraw :
          rawCoreBudget n n ≤ 16384 * (n + 1) ^ 3 :=
        root_rawCoreBudget_le n
      have hlin : n + 7 ≤ 7 * (n + 1) ^ 3 :=
        linear_le_cube_budget n
      have hT :
          total ≤ rawVerifierTimeBound n := by
        have hm' : m ≤ 16384 * (n + 1) ^ 3 :=
          Nat.le_trans hm hraw
        unfold rawVerifierTimeBound
        omega
      refine ⟨total, ?_, ?_, ?_⟩
      · simpa [n] using hT
      · simpa [n] using hhalt
      · simpa [n] using hnot

/-- A successful bounded decode with nonempty residual source is also
fail-closed: either the decoded prefix is syntactically invalid and the exact
negative producer rejects it, or it is syntactically valid and the mandatory
source-empty guard rejects the residual tail. -/
theorem prepared_residual_fail_closed
    (source witness : BitString)
    (hw : witness.length = source.length)
    (phi : Circuit) (tail : BitString)
    (hne : tail ≠ [])
    (hcore :
      decodeCircuitCore (source.length + 1) source =
        some (phi, tail)) :
    ∃ total ≤ rawVerifierTimeBound source.length,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  have hsound :
      source = encodeCircuit phi ++ tail :=
    decodeCircuitCore_sound (source.length + 1) source phi tail hcore
  have hsourceNonempty : source ≠ [] := by
    rw [hsound]
    cases phi <;> simp [encodeCircuit]
  cases source with
  | nil => contradiction
  | cons b bs =>
      let n := (b :: bs).length
      have henc :
          (encodeCircuit phi).length ≤ n := by
        have hlen : (encodeCircuit phi).length ≤
            (encodeCircuit phi ++ tail).length := by simp
        simpa [n, hsound] using hlen
      have hlenPhi : varBound phi ≤ witness.length := by
        rw [hw]
        exact Nat.le_trans (varBound_le_encoded_length phi)
          (by simpa [n] using henc)
      have hLayout :
          CheckedLayoutBound n 0
            (encodeCircuit phi ++ tail) (encodeEvalFrames []) := by
        constructor
        · simpa [n, hsound]
        · simp
      cases hmode : modeCheck .cnf phi with
      | false =>
          have hrej :=
            circuit_exact_bounded_reject
              (rawAssignment witness) witness phi .cnf
          obtain ⟨m, hm, cfg, hreach, hrejState⟩ :=
            hrej hmode tail [] 0 0 n hLayout hlenPhi
              (by intro i hi; rfl)
          have hreach' :
              cfg ∈ checkedEvalRunLoopMachine.runBranches m
                [{ state := checkedEvalRunLoopMachine.initial,
                   tape :=
                     evalCursorStackEndTape witness 0 (b :: bs) [] 0 }] := by
            simpa [checkedEvalRunLoopMachine, hsound] using hreach
          obtain ⟨total, htotal, hhalt, hnot⟩ :=
            lift_eval_raw_failure witness b bs m cfg hreach'
              (Or.inl hrejState)
          have hcb :=
            checkedCircuitBudget_le_exact_global n phi henc
          have hlin := linear_le_cube_budget n
          have hT : total ≤ rawVerifierTimeBound n := by
            unfold rawVerifierTimeBound
            omega
          exact ⟨total, by simpa [n] using hT,
            by simpa [n] using hhalt,
            by simpa [n] using hnot⟩
      | true =>
          obtain ⟨m, hm, cfg, hreach, hrejState⟩ :=
            canonical_prefix_with_residual_reaches_reject
              (rawAssignment witness) witness phi tail hne hmode n
              hLayout hlenPhi (by intro i hi; rfl)
          have hreach' :
              cfg ∈ checkedEvalRunLoopMachine.runBranches m
                [{ state := checkedEvalRunLoopMachine.initial,
                   tape :=
                     evalCursorStackEndTape witness 0 (b :: bs) [] 0 }] := by
            simpa [checkedEvalRunLoopMachine, hsound] using hreach
          obtain ⟨total, htotal, hhalt, hnot⟩ :=
            lift_eval_raw_failure witness b bs m cfg hreach'
              (Or.inl hrejState)
          have hcb :=
            checkedCircuitBudget_le_exact_global n phi henc
          have hlin := linear_le_cube_budget n
          have hT : total ≤ rawVerifierTimeBound n := by
            unfold rawVerifierTimeBound
            omega
          exact ⟨total, by simpa [n] using hT,
            by simpa [n] using hhalt,
            by simpa [n] using hnot⟩

/-- Exact fail-closed theorem for every source rejected by the canonical whole
decoder. -/
theorem rawSourceClosure_at_some_fuel
    (source witness : BitString)
    (hw : witness.length = source.length)
    (hdecode : decodeCircuit source = none) :
    ∃ total ≤ rawVerifierTimeBound source.length,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  unfold decodeCircuit at hdecode
  cases hcore :
      decodeCircuitCore (source.length + 1) source with
  | none =>
      exact prepared_core_none_fail_closed source witness hw hcore
  | some p =>
      rcases p with ⟨phi, tail⟩
      cases tail with
      | nil =>
          simp [hcore] at hdecode
      | cons b bs =>
          apply prepared_residual_fail_closed
            source witness hw phi (b :: bs) (by simp) hcore

/-- Once a deterministic verifier has halted, acceptance at larger fuel is
equivalent to acceptance at the halting fuel. -/
theorem acceptsWithin_iff_of_haltsWithin_mono
    (n m : Nat)
    (start : VerifierConfig)
    (hnm : n ≤ m)
    (hhalt : checkedVerifierMachine.HaltsWithin n start) :
    checkedVerifierMachine.AcceptsWithin m start ↔
      checkedVerifierMachine.AcceptsWithin n start := by
  constructor
  · rintro ⟨z, hz, hacc⟩
    have hzhalt : Halted checkedVerifierMachine z :=
      halted_of_accepting checkedVerifierMachine z hacc
    have hzsmall :=
      mem_of_haltsWithin checkedVerifierMachine n m
        start z hnm hz hzhalt
    exact ⟨z, hzsmall, hacc⟩
  · rintro ⟨z, hz, hacc⟩
    have hzhalt : Halted checkedVerifierMachine z :=
      halted_of_accepting checkedVerifierMachine z hacc
    have hp :=
      mem_runBranches_persist checkedVerifierMachine
        n (m - n) [start] z hz hzhalt
    have heq : n + (m - n) = m := by omega
    rw [heq] at hp
    exact ⟨z, hp, hacc⟩

/-- Raw decoder failure at the final fixed cubic fuel. -/
theorem rawSourceClosure
    (source witness : BitString)
    (hw : witness.length = source.length)
    (hdecode : decodeCircuit source = none) :
    checkedVerifierMachine.HaltsWithin
        (rawVerifierTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin
        (rawVerifierTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  obtain ⟨m, hm, hhalt, hnot⟩ :=
    rawSourceClosure_at_some_fuel source witness hw hdecode
  constructor
  · exact haltsWithin_mono_le checkedVerifierMachine m
      (rawVerifierTimeBound source.length) hm hhalt
  · exact not_acceptsWithin_mono_after_halt
      m (rawVerifierTimeBound source.length)
      { state := checkedVerifierMachine.initial,
        tape := preparedTape witness source }
      hm hhalt hnot

/-- Total checked-verifier correctness for arbitrary raw bitstrings at one
uniform polynomial fuel. -/
theorem checked_total
    (source witness : BitString)
    (hw : witness.length = source.length) :
    checkedVerifierMachine.HaltsWithin
        (rawVerifierTimeBound source.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      (checkedVerifierMachine.AcceptsWithin
          (rawVerifierTimeBound source.length)
          { state := checkedVerifierMachine.initial,
            tape := preparedTape witness source } ↔
        VerifyBits source witness) := by
  rcases P01RawSourceSplit.exact_encoding_or_decode_none source with
      hcanonical | hraw
  · rcases hcanonical with ⟨phi, rfl⟩
    have hlen : varBound phi ≤ witness.length := by
      rw [hw]
      exact varBound_le_encoded_length phi
    let T0 := checkedVerifierExactTimeBound (encodeCircuit phi).length
    let T := rawVerifierTimeBound (encodeCircuit phi).length
    have hle : T0 ≤ T := exactTimeBound_le_raw _
    have hhalt0 :=
      prepared_canonical_halts_within_exact_global witness phi hlen
    have hcorr0 :=
      prepared_canonical_accepts_iff_exact_global witness phi hlen
    constructor
    · exact haltsWithin_mono_le checkedVerifierMachine T0 T hle
        (by simpa [T0] using hhalt0)
    · have hiff :=
        acceptsWithin_iff_of_haltsWithin_mono T0 T
          { state := checkedVerifierMachine.initial,
            tape := preparedTape witness (encodeCircuit phi) }
          hle (by simpa [T0] using hhalt0)
      exact hiff.trans (by simpa [T0] using hcorr0)
  · have hfc := rawSourceClosure source witness hw hraw
    constructor
    · exact hfc.1
    · constructor
      · intro hacc
        exact False.elim (hfc.2 hacc)
      · intro hver
        exact False.elim
          ((P01RawSourceSplit.verifyBits_false_of_decode_none
            source witness hraw) hver)

/-- The unique remaining verifier phase is now inhabited. -/
noncomputable def verifierPhase :
    P01VerifierPhase prepPhase.layout where
  stateCount := checkedVerifierStateCount
  machine := checkedVerifierFinMachine
  blank_none := checkedVerifierFinMachine_blank
  timeBound := rawVerifierTimeBound
  time_poly := rawVerifierTimeBound_poly
  halts := by
    intro bs w hw
    have h := (checked_total bs w hw).1
    have hfin :=
      (checkedVerifierFinMachine_haltsWithin_iff
        (rawVerifierTimeBound bs.length)
        ({ state := checkedVerifierMachine.initial,
           tape := preparedTape w bs } : VerifierConfig)).2 h
    change checkedVerifierFinMachine.HaltsWithin
      (rawVerifierTimeBound bs.length)
      (liftConfig checkedVerifierStateEncode
        ({ state := checkedVerifierMachine.initial,
           tape := preparedTape w bs } : VerifierConfig))
    exact hfin
  correct := by
    intro bs w hw
    have h := (checked_total bs w hw).2
    have hfin :=
      checkedVerifierFinMachine_acceptsWithin_iff
        (rawVerifierTimeBound bs.length)
        ({ state := checkedVerifierMachine.initial,
           tape := preparedTape w bs } : VerifierConfig)
    change
      (checkedVerifierFinMachine.AcceptsWithin
          (rawVerifierTimeBound bs.length)
          (liftConfig checkedVerifierStateEncode
            ({ state := checkedVerifierMachine.initial,
               tape := preparedTape w bs } : VerifierConfig)) ↔
        VerifyBits bs w)
    exact hfin.trans h

/-- P01 construction gap closed by the actual prep and verifier inhabitants. -/
theorem p01ConstructionGap_closed :
    P01FinalCertificate.P01ConstructionGap :=
  p01_of_verifier verifierPhase

#print axioms MCore.Real.P01RawSourceClosure.rawSourceClosure
#print axioms MCore.Real.P01RawSourceClosure.checked_total
#print axioms MCore.Real.P01RawSourceClosure.verifierPhase
#print axioms MCore.Real.P01RawSourceClosure.p01ConstructionGap_closed

end P01RawSourceClosure
end Real
end MCore
