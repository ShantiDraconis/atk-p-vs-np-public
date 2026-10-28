import MCore.Real.P01ExactBoundedCircuitProducer
import MCore.Real.P01ExactVerifierGlobalBudget
import MCore.Real.P01CheckedVerifierCompositeNTM
import MCore.Real.P01CheckedVerifierRun
import MCore.Real.P01CheckedVerifierDeterminism
import MCore.Real.P01ExactBoundedReject
import MCore.Real.P01DirectVerifierInhabitant

namespace MCore
namespace Real
namespace P01ExactVerifierCanonicalRun

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01EvalCursorMachine
open P01EncodedFrameTape
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedVerifierInvariant
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierRun
open P01CheckedVerifierDeterminism
open P01ExactBoundedCircuitProducer
open P01ExactVerifierGlobalBudget
open P01ExactBoundedReject
open P01DirectVerifierInhabitant
open P01WitnessPreservingPrep
open P01NTMRunLaws

abbrev CheckedVerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

/-- The scanner/entry prefix is absorbed by the exact verifier's reserved
quadratic overhead. -/
theorem scan_entry_le_exact_allowance
    (n : Nat) :
    n + 3 ≤ 256 * (n + 1) ^ 2 := by
  have h1 : n + 3 ≤ 4 * (n + 1) := by omega
  have hsq : n + 1 ≤ (n + 1) ^ 2 := by
    have hpos : 1 ≤ n + 1 := by omega
    calc
      n + 1 = (n + 1) * 1 := by simp
      _ ≤ (n + 1) * (n + 1) :=
        Nat.mul_le_mul_left (n + 1) hpos
      _ = (n + 1) ^ 2 := by
        simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have h4 := Nat.mul_le_mul_left 4 hsq
  calc
    n + 3 ≤ 4 * (n + 1) := h1
    _ ≤ 4 * (n + 1) ^ 2 := h4
    _ ≤ 256 * (n + 1) ^ 2 := by
      exact Nat.mul_le_mul_right ((n + 1) ^ 2) (by omega)

/-- Valid canonical CNF sources reach the semantic final state within one
uniform cubic fuel.  This is the quantitative whole-verifier adapter from the
exact recursive producer. -/
theorem prepared_cnf_reaches_semantic_final_within_exact_global
    (sigma : Assignment)
    (witness : BitString)
    (phi : Circuit)
    (hmode : modeCheck .cnf phi = true)
    (hlen : varBound phi ≤ witness.length)
    (hread :
      ∀ i, i < varBound phi →
        witness.getD i false = sigma i) :
    ∃ m ≤ checkedVerifierExactTimeBound (encodeCircuit phi).length,
      ∃ tape,
        ({ state := .eval (.final (evalCircuit sigma phi)),
           tape := tape } : CheckedVerifierConfig) ∈
          checkedVerifierMachine.runBranches m
            [{ state := checkedVerifierMachine.initial,
               tape := preparedTape witness (encodeCircuit phi) }] := by
  have hne : encodeCircuit phi ≠ [] := by
    cases phi with
    | input i => simp [encodeCircuit]
    | const b => cases b <;> simp [encodeCircuit]
    | not child => simp [encodeCircuit]
    | and a b => simp [encodeCircuit]
    | or a b => simp [encodeCircuit]
  cases hsrc : encodeCircuit phi with
  | nil =>
      exact False.elim (hne hsrc)
  | cons b bs =>
      let n := (b :: bs).length
      obtain ⟨m0, hm0, h0⟩ :=
        prepared_nonempty_reaches_eval_start witness b bs

      have hLayout :
          CheckedLayoutBound n 0
            (encodeCircuit phi ++ ([] : BitString))
            (encodeEvalFrames []) := by
        constructor
        · simp [n, hsrc]
        · simp

      have hcert :=
        circuit_exact_bounded_certificate sigma witness phi .cnf
      obtain ⟨m1, hm1, cfg1, h1, hout1⟩ :=
        hcert hmode [] [] 0 0 n hLayout hlen hread

      have h1src :
          cfg1 ∈
            checkedEvalRunLoopMachine.runBranches m1
              [{ state := checkedEvalRunLoopMachine.initial,
                 tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }] := by
        simpa [checkedEvalRunLoopMachine, hsrc] using h1

      simp [ExactCheckedLoopOutcome] at hout1
      rcases hout1 with ⟨tape1, hcfg1⟩
      subst cfg1

      have hLift :
          ({ state := .eval (.final (evalCircuit sigma phi)),
             tape := tape1 } : CheckedVerifierConfig) ∈
            checkedVerifierMachine.runBranches m1
              [({ state := .eval checkedEvalRunLoopMachine.initial,
                  tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
                CheckedVerifierConfig)] := by
        have hlift :=
          checked_eval_mem_lift m1
            ({ state := checkedEvalRunLoopMachine.initial,
               tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
              Configuration CheckedEvalRunState (Option Bool))
            ({ state := .final (evalCircuit sigma phi),
               tape := tape1 } :
              Configuration CheckedEvalRunState (Option Bool))
            h1src
        simpa [checkedEvalEmbed, P01NTMRunLaws.liftConfig] using hlift

      have hAll :=
        mem_runBranches_trans checkedVerifierMachine
          m0 m1
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (b :: bs) }]
          ({ state := .eval checkedEvalRunLoopMachine.initial,
             tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
            CheckedVerifierConfig)
          ({ state := .eval (.final (evalCircuit sigma phi)),
             tape := tape1 } : CheckedVerifierConfig)
          h0 hLift

      have hscan :
          m0 ≤ 256 * (n + 1) ^ 2 :=
        Nat.le_trans hm0 (scan_entry_le_exact_allowance n)

      have hbudget :
          m0 + m1 ≤ checkedVerifierExactTimeBound n := by
        have henc : (encodeCircuit phi).length ≤ n := by
          simp [n, hsrc]
        have hcap :=
          exact_evaluation_plus_scan_le_global n phi henc
        omega

      refine ⟨m0 + m1, ?_, tape1, ?_⟩
      · simpa [n, hsrc] using hbudget
      · simpa [hsrc] using hAll


/-- Canonical circuits that fail the CNF grammar reach physical reject under
the same global cubic envelope. -/
theorem prepared_invalid_canonical_reaches_reject_within_exact_global
    (witness : BitString)
    (phi : Circuit)
    (hlen : varBound phi ≤ witness.length)
    (hinvalid : modeCheck .cnf phi = false) :
    ∃ m ≤ checkedVerifierExactTimeBound (encodeCircuit phi).length,
      ∃ tape,
        ({ state := .reject, tape := tape } : CheckedVerifierConfig) ∈
          checkedVerifierMachine.runBranches m
            [{ state := checkedVerifierMachine.initial,
               tape := preparedTape witness (encodeCircuit phi) }] := by
  have hne : encodeCircuit phi ≠ [] := by
    cases phi with
    | input i => simp [encodeCircuit]
    | const b => cases b <;> simp [encodeCircuit]
    | not child => simp [encodeCircuit]
    | and a b => simp [encodeCircuit]
    | or a b => simp [encodeCircuit]
  cases hsrc : encodeCircuit phi with
  | nil =>
      exact False.elim (hne hsrc)
  | cons b bs =>
      let n := (b :: bs).length
      obtain ⟨m0, hm0, h0⟩ :=
        prepared_nonempty_reaches_eval_start witness b bs

      have hLayout :
          CheckedLayoutBound n 0
            (encodeCircuit phi ++ ([] : BitString))
            (encodeEvalFrames []) := by
        constructor
        · simp [n, hsrc]
        · simp

      have hcert :=
        circuit_exact_bounded_reject
          (witnessAssignment witness) witness phi .cnf
      obtain ⟨m1, hm1, cfg1, h1, hrej⟩ :=
        hcert hinvalid [] [] 0 0 n hLayout hlen (by
          intro i hi
          rfl)

      have h1src :
          cfg1 ∈
            checkedEvalRunLoopMachine.runBranches m1
              [{ state := checkedEvalRunLoopMachine.initial,
                 tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }] := by
        simpa [checkedEvalRunLoopMachine, hsrc] using h1

      have hLift :=
        checked_eval_mem_lift m1
          ({ state := checkedEvalRunLoopMachine.initial,
             tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
            Configuration CheckedEvalRunState (Option Bool))
          cfg1 h1src

      rcases cfg1 with ⟨q, tape1⟩
      change q = .reject at hrej
      subst q

      have hLift' :
          ({ state := .reject, tape := tape1 } : CheckedVerifierConfig) ∈
            checkedVerifierMachine.runBranches m1
              [({ state := .eval checkedEvalRunLoopMachine.initial,
                  tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
                CheckedVerifierConfig)] := by
        simpa [checkedEvalEmbed, P01NTMRunLaws.liftConfig] using hLift

      have hAll :=
        mem_runBranches_trans checkedVerifierMachine
          m0 m1
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (b :: bs) }]
          ({ state := .eval checkedEvalRunLoopMachine.initial,
             tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
            CheckedVerifierConfig)
          ({ state := .reject, tape := tape1 } : CheckedVerifierConfig)
          h0 hLift'

      have hscan :
          m0 ≤ 256 * (n + 1) ^ 2 :=
        Nat.le_trans hm0 (scan_entry_le_exact_allowance n)

      have hbudget :
          m0 + m1 ≤ checkedVerifierExactTimeBound n := by
        have henc : (encodeCircuit phi).length ≤ n := by
          simp [n, hsrc]
        have hcap :=
          exact_evaluation_plus_scan_le_global n phi henc
        omega

      refine ⟨m0 + m1, ?_, tape1, ?_⟩
      · simpa [n, hsrc] using hbudget
      · simpa [hsrc] using hAll

/-- Every canonical source halts by the single exact global cubic bound. -/
theorem prepared_canonical_halts_within_exact_global
    (witness : BitString)
    (phi : Circuit)
    (hlen : varBound phi ≤ witness.length) :
    checkedVerifierMachine.HaltsWithin
      (checkedVerifierExactTimeBound (encodeCircuit phi).length)
      { state := checkedVerifierMachine.initial,
        tape := preparedTape witness (encodeCircuit phi) } := by
  let T := checkedVerifierExactTimeBound (encodeCircuit phi).length
  cases hmode : modeCheck .cnf phi with
  | false =>
      obtain ⟨m, hm, tape, hreach⟩ :=
        prepared_invalid_canonical_reaches_reject_within_exact_global
          witness phi hlen hmode
      have hhalt :
          Halted checkedVerifierMachine
            ({ state := .reject, tape := tape } : CheckedVerifierConfig) := by
        simp [Halted, checkedVerifierMachine]
      have hmhalt :=
        haltsWithin_of_reaches_halted m
          { state := checkedVerifierMachine.initial,
            tape := preparedTape witness (encodeCircuit phi) }
          ({ state := .reject, tape := tape } : CheckedVerifierConfig)
          hreach hhalt
      exact haltsWithin_mono_le checkedVerifierMachine m T
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (encodeCircuit phi) }
        (by simpa [T] using hm) hmhalt
  | true =>
      obtain ⟨m, hm, tape, hreach⟩ :=
        prepared_cnf_reaches_semantic_final_within_exact_global
          (witnessAssignment witness) witness phi hmode hlen (by
            intro i hi
            rfl)
      have hhalt :
          Halted checkedVerifierMachine
            ({ state :=
                 .eval (.final
                   (evalCircuit (witnessAssignment witness) phi)),
               tape := tape } : CheckedVerifierConfig) := by
        unfold Halted
        cases hval : evalCircuit (witnessAssignment witness) phi <;>
          simp [checkedVerifierMachine, checkedEvalRunLoopMachine, hval]
      have hmhalt :=
        haltsWithin_of_reaches_halted m
          { state := checkedVerifierMachine.initial,
            tape := preparedTape witness (encodeCircuit phi) }
          ({ state :=
               .eval (.final
                 (evalCircuit (witnessAssignment witness) phi)),
             tape := tape } : CheckedVerifierConfig)
          hreach hhalt
      exact haltsWithin_mono_le checkedVerifierMachine m T
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (encodeCircuit phi) }
        (by simpa [T] using hm) hmhalt

/-- Canonical-source correctness at the fixed global fuel, not merely at an
existentially chosen stopping time. -/
theorem prepared_canonical_accepts_iff_exact_global
    (witness : BitString)
    (phi : Circuit)
    (hlen : varBound phi ≤ witness.length) :
    checkedVerifierMachine.AcceptsWithin
        (checkedVerifierExactTimeBound (encodeCircuit phi).length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (encodeCircuit phi) } ↔
      P01GuessedWitnessRelation.VerifyBits (encodeCircuit phi) witness := by
  let T := checkedVerifierExactTimeBound (encodeCircuit phi).length
  let start : CheckedVerifierConfig :=
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness (encodeCircuit phi) }
  cases hmode : modeCheck .cnf phi with
  | false =>
      obtain ⟨m, hm, tape, hreach⟩ :=
        prepared_invalid_canonical_reaches_reject_within_exact_global
          witness phi hlen hmode
      let terminal : CheckedVerifierConfig :=
        { state := .reject, tape := tape }
      have hhalt : Halted checkedVerifierMachine terminal := by
        simp [terminal, Halted, checkedVerifierMachine]
      have hreachT :
          terminal ∈ checkedVerifierMachine.runBranches T [start] := by
        have hp :=
          mem_runBranches_persist checkedVerifierMachine
            m (T - m) [start] terminal
            (by simpa [start, terminal] using hreach) hhalt
        have heq : m + (T - m) = T := by
          have : m ≤ T := by simpa [T] using hm
          omega
        simpa [heq] using hp
      rw [acceptsWithin_iff_of_reached_terminal T start terminal hreachT,
        verifyBits_encode_iff]
      have hnotcnf : ¬ IsCNF phi := by
        intro hcnf
        have ht := (modeCheck_cnf_iff phi).2 hcnf
        rw [hmode] at ht
        cases ht
      constructor
      · intro hacc
        have hrejt :
            checkedVerifierMachine.accepting terminal.state = false := by
          simp [terminal, checkedVerifierMachine]
        rw [hrejt] at hacc
        cases hacc
      · rintro ⟨hcnf, heval⟩
        exact False.elim (hnotcnf hcnf)
  | true =>
      obtain ⟨m, hm, tape, hreach⟩ :=
        prepared_cnf_reaches_semantic_final_within_exact_global
          (witnessAssignment witness) witness phi hmode hlen (by
            intro i hi
            rfl)
      let value := evalCircuit (witnessAssignment witness) phi
      let terminal : CheckedVerifierConfig :=
        { state := .eval (.final value), tape := tape }
      have hhalt : Halted checkedVerifierMachine terminal := by
        unfold terminal value Halted
        cases hval : evalCircuit (witnessAssignment witness) phi <;>
          simp [checkedVerifierMachine, checkedEvalRunLoopMachine, hval]
      have hreachT :
          terminal ∈ checkedVerifierMachine.runBranches T [start] := by
        have hp :=
          mem_runBranches_persist checkedVerifierMachine
            m (T - m) [start] terminal
            (by simpa [start, terminal, value] using hreach) hhalt
        have heq : m + (T - m) = T := by
          have : m ≤ T := by simpa [T] using hm
          omega
        simpa [heq] using hp
      rw [acceptsWithin_iff_of_reached_terminal T start terminal hreachT]
      have hcnf : IsCNF phi :=
        (modeCheck_cnf_iff phi).1 hmode
      cases hval : evalCircuit (witnessAssignment witness) phi <;>
        simp [terminal, value, checkedVerifierMachine,
          checkedEvalRunLoopMachine, verifyBits_encode_iff,
          witnessAssignment, hcnf, hval]


#print axioms MCore.Real.P01ExactVerifierCanonicalRun.scan_entry_le_exact_allowance
#print axioms MCore.Real.P01ExactVerifierCanonicalRun.prepared_cnf_reaches_semantic_final_within_exact_global

end P01ExactVerifierCanonicalRun
end Real
end MCore
