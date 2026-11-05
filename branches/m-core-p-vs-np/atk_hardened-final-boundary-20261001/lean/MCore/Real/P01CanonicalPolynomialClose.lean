import MCore.Real.P01ExactOrBounded
import MCore.Real.P01CheckedVerifierFiniteState
import MCore.Real.P01CheckedVerifierRun
import MCore.Real.P01DirectVerifierInhabitant

namespace MCore
namespace Real
namespace P01CanonicalPolynomialClose

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open CanonicalSATVerifier
open P01CNFMode
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierFiniteState
open P01CheckedVerifierInvariant
open P01CheckedVerifierGlobalBudget
open P01ExactBoundedCircuitProducer
open P01ExactOrBounded
open P01NTMRunLaws
open P01WitnessPreservingPrep
open P01DirectVerifierInhabitant

/-- Conservative cubic bound for the complete valid-CNF physical verifier. -/
def canonicalVerifierTimeBound : TimeBound :=
  fun n => 16384 * (n + 1) ^ 3

theorem canonicalVerifierTimeBound_poly :
    PolynomialTimeBound canonicalVerifierTimeBound := by
  exact ⟨16384, 3, fun n => Nat.le_refl _⟩

theorem checkedCircuitBudget_le_cubic
    (phi : Circuit) :
    checkedCircuitBudget phi (encodeCircuit phi).length
      ≤ 8192 * ((encodeCircuit phi).length + 1) ^ 3 := by
  let n := (encodeCircuit phi).length
  have hs : evalStepCount phi ≤ 3 * n := by
    simpa [n] using evalStepCount_le_three_mul_encoding phi
  unfold checkedCircuitBudget checkedLoopStepEnvelope
  have hcoef : 8 * (evalStepCount phi + 1) * 256 ≤
      8192 * (n + 1) := by
    omega
  have hmul := Nat.mul_le_mul_right ((n + 1) ^ 2) hcoef
  simpa [n, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    using hmul

theorem scan_prefix_le_cubic (n : Nat) :
    n + 3 ≤ 8192 * (n + 1) ^ 3 := by
  have h1 : 1 ≤ (n + 1)^3 := by positivity
  omega

/-- Valid canonical CNF input reaches the correct terminal state within the
    explicit global cubic bound. -/
theorem valid_cnf_reaches_terminal_within
    (witness : BitString)
    (phi : Circuit)
    (hmode : modeCheck .cnf phi = true)
    (hlen : varBound phi ≤ witness.length) :
    ∃ terminal : CheckedVerifierConfig,
      terminal ∈ checkedVerifierMachine.runBranches
        (canonicalVerifierTimeBound (encodeCircuit phi).length)
        [{ state := checkedVerifierMachine.initial,
           tape := preparedTape witness (encodeCircuit phi) }] ∧
      Halted checkedVerifierMachine terminal ∧
      (checkedVerifierMachine.accepting terminal.state = true ↔
        VerifyBits (encodeCircuit phi) witness) := by
  let n := (encodeCircuit phi).length
  have hne : encodeCircuit phi ≠ [] := by
    cases phi <;> simp [encodeCircuit]
  cases hsrc : encodeCircuit phi with
  | nil => exact False.elim (hne hsrc)
  | cons b bs =>
      obtain ⟨m0, hm0, h0⟩ :=
        prepared_nonempty_reaches_eval_start witness b bs
      let cEval : Configuration CheckedEvalRunState (Option Bool) :=
        { state := checkedEvalRunLoopMachine.initial,
          tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }
      have hroot :
          CheckedLayoutBound n 0 (encodeCircuit phi) [] := by
        simpa [n] using P01CheckedVerifierInvariant.root (encodeCircuit phi)
      have hcert :=
        circuit_exact_bounded_certificate
          (witnessAssignment witness) witness phi .cnf
      obtain ⟨m1, hm1, cfg1, h1, hout1⟩ :=
        hcert hmode [] [] 0 0 n hroot hlen (by
          intro i hi
          rfl)
      have h1src :
          cfg1 ∈ checkedEvalRunLoopMachine.runBranches m1 [cEval] := by
        simpa [cEval, hsrc] using h1
      have h1lift :
          ({ state := checkedEvalEmbed cfg1.state, tape := cfg1.tape } :
            CheckedVerifierConfig) ∈
          checkedVerifierMachine.runBranches m1
            [({ state := .eval checkedEvalRunLoopMachine.initial,
               tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
              CheckedVerifierConfig)] := by
        have hmap := checked_eval_mem_lift m1 cEval cfg1 h1src
        simpa [cEval, P01NTMRunLaws.liftConfig] using hmap
      let terminal : CheckedVerifierConfig :=
        { state := checkedEvalEmbed cfg1.state, tape := cfg1.tape }
      have hreachSmall :
          terminal ∈ checkedVerifierMachine.runBranches (m0 + m1)
            [{ state := checkedVerifierMachine.initial,
               tape := preparedTape witness (encodeCircuit phi) }] := by
        have ht := mem_runBranches_trans checkedVerifierMachine
          m0 m1
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (encodeCircuit phi) }]
          ({ state := .eval checkedEvalRunLoopMachine.initial,
             tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
             CheckedVerifierConfig)
          terminal
          (by simpa [hsrc] using h0)
          (by simpa [terminal] using h1lift)
        exact ht
      have hout :
          ∃ tape, cfg1 =
            { state := .final (evalCircuit (witnessAssignment witness) phi),
              tape := tape } := by
        simpa [ExactCheckedLoopOutcome] using hout1
      rcases hout with ⟨tape, hcfg⟩
      subst cfg1
      have hhalt : Halted checkedVerifierMachine terminal := by
        unfold terminal Halted
        cases hv : evalCircuit (witnessAssignment witness) phi <;>
          simp [checkedEvalEmbed, checkedVerifierMachine,
            checkedEvalRunLoopMachine, hv]
      have hm0' : m0 ≤ 8192 * (n + 1)^3 := by
        have hlenEq : (b :: bs).length = n := by
          simpa [n, hsrc]
        rw [hlenEq] at hm0
        exact Nat.le_trans hm0 (scan_prefix_le_cubic n)
      have hm1' : m1 ≤ 8192 * (n + 1)^3 :=
        Nat.le_trans hm1 (by
          simpa [n] using checkedCircuitBudget_le_cubic phi)
      have hsum : m0 + m1 ≤ canonicalVerifierTimeBound n := by
        unfold canonicalVerifierTimeBound
        omega
      have hpersist :
          terminal ∈ checkedVerifierMachine.runBranches
            (canonicalVerifierTimeBound n)
            [{ state := checkedVerifierMachine.initial,
               tape := preparedTape witness (encodeCircuit phi) }] := by
        have hk :
            canonicalVerifierTimeBound n =
              (m0 + m1) + (canonicalVerifierTimeBound n - (m0 + m1)) := by
          omega
        rw [hk]
        exact mem_runBranches_persist checkedVerifierMachine
          (m0 + m1)
          (canonicalVerifierTimeBound n - (m0 + m1))
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (encodeCircuit phi) }]
          terminal hreachSmall hhalt
      refine ⟨terminal, ?_, hhalt, ?_⟩
      · simpa [n] using hpersist
      · rw [verifyBits_encode_iff]
        have hcnf : IsCNF phi := (modeCheck_cnf_iff phi).1 hmode
        constructor
        · intro hacc
          exact ⟨hcnf, by
            change checkedEvalRunLoopMachine.accepting
              (.final (evalCircuit (witnessAssignment witness) phi)) = true at hacc
            simpa [checkedEvalRunLoopMachine] using hacc⟩
        · rintro ⟨_, heval⟩
          change checkedEvalRunLoopMachine.accepting
            (.final (evalCircuit (witnessAssignment witness) phi)) = true
          simpa [checkedEvalRunLoopMachine, heval]

#print axioms MCore.Real.P01CanonicalPolynomialClose.checkedCircuitBudget_le_cubic
#print axioms MCore.Real.P01CanonicalPolynomialClose.valid_cnf_reaches_terminal_within

end P01CanonicalPolynomialClose
end Real
end MCore
