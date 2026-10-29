import MCore.Real.P01CheckedVerifierCompositeNTM
import MCore.Real.P01CheckedEvalRunCircuitCertificate
import MCore.Real.CanonicalSATWitness
import MCore.Real.CanonicalSATVerifier

namespace MCore
namespace Real
namespace P01CheckedVerifierRun

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open CanonicalSATVerifier
open P01CNFMode
open P01EvalCursorMachine
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunCircuitCertificate
open P01CheckedVerifierCompositeNTM
open P01WitnessPreservingPrep
open P01NTMRunLaws

abbrev CheckedVerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

theorem checked_eval_mem_lift
    (n : Nat)
    (a b : Configuration CheckedEvalRunState (Option Bool))
    (h :
      b ∈ checkedEvalRunLoopMachine.runBranches n [a]) :
    P01NTMRunLaws.liftConfig checkedEvalEmbed b ∈
      checkedVerifierMachine.runBranches n
        [P01NTMRunLaws.liftConfig checkedEvalEmbed a] := by
  rw [show
    [P01NTMRunLaws.liftConfig checkedEvalEmbed a] =
      [a].map (P01NTMRunLaws.liftConfig checkedEvalEmbed) by rfl]
  rw [checked_eval_runBranches_map]
  exact List.mem_map.mpr ⟨b, h, rfl⟩

private theorem encodeCircuit_ne_nil
    (phi : Circuit) :
    encodeCircuit phi ≠ [] := by
  cases phi with
  | input i =>
      simp [encodeCircuit]
  | const b =>
      cases b <;> simp [encodeCircuit]
  | not c =>
      simp [encodeCircuit]
  | and a b =>
      simp [encodeCircuit]
  | or a b =>
      simp [encodeCircuit]

/-- Valid-CNF prepared circuits reach the semantic Boolean in the checked
verifier wrapper.

This is the first whole-verifier run theorem for the checked machine.  The only
assumptions are exactly the syntax firewall and the finite witness agreement
required by the checked circuit certificate. -/
theorem prepared_cnf_reaches_semantic_final
    (sigma : Assignment)
    (witness : BitString)
    (phi : Circuit)
    (hmode : modeCheck .cnf phi = true)
    (hlen : varBound phi ≤ witness.length)
    (hread :
      ∀ i, i < varBound phi →
        witness.getD i false = sigma i) :
    ∃ m tape,
      ({ state :=
           .eval (.final (evalCircuit sigma phi)),
         tape := tape } : CheckedVerifierConfig) ∈
        checkedVerifierMachine.runBranches m
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (encodeCircuit phi) }] := by
  have hne : encodeCircuit phi ≠ [] :=
    encodeCircuit_ne_nil phi
  cases hsrc : encodeCircuit phi with
  | nil =>
      exact False.elim (hne hsrc)
  | cons b bs =>
      obtain ⟨m0, hm0, h0⟩ :=
        prepared_nonempty_reaches_eval_start witness b bs

      let cEval : Configuration CheckedEvalRunState (Option Bool) :=
        { state := checkedEvalRunLoopMachine.initial,
          tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }

      have h0' :
          ({ state := .eval checkedEvalRunLoopMachine.initial,
             tape := evalCursorStackEndTape witness 0
               (b :: bs) [] 0 } : CheckedVerifierConfig) ∈
            checkedVerifierMachine.runBranches m0
              [{ state := checkedVerifierMachine.initial,
                 tape := preparedTape witness (b :: bs) }] := by
        exact h0

      have hcert :=
        circuit_certificate sigma witness phi .cnf
      obtain ⟨m1, cfg1, h1, hout1⟩ :=
        hcert hmode [] [] 0 0 hlen hread

      have h1src :
          cfg1 ∈
            checkedEvalRunLoopMachine.runBranches m1 [cEval] := by
        simpa [cEval, hsrc] using h1

      rcases hout1 with ⟨tape1, hcfg1⟩
      subst cfg1

      have hLift :
          ({ state := .eval (.final (evalCircuit sigma phi)),
             tape := tape1 } : CheckedVerifierConfig) ∈
            checkedVerifierMachine.runBranches m1
              [({ state := .eval checkedEvalRunLoopMachine.initial,
                  tape := evalCursorStackEndTape witness 0
                    (b :: bs) [] 0 } :
                CheckedVerifierConfig)] := by
        have hlift :=
          checked_eval_mem_lift m1 cEval
            ({ state := .final (evalCircuit sigma phi),
               tape := tape1 } :
              Configuration CheckedEvalRunState (Option Bool))
            h1src
        simpa [cEval, checkedEvalEmbed, P01NTMRunLaws.liftConfig] using hlift

      have hAll :=
        mem_runBranches_trans checkedVerifierMachine
          m0 m1
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (b :: bs) }]
          ({ state := .eval checkedEvalRunLoopMachine.initial,
             tape := evalCursorStackEndTape witness 0
               (b :: bs) [] 0 } : CheckedVerifierConfig)
          ({ state := .eval (.final (evalCircuit sigma phi)),
             tape := tape1 } : CheckedVerifierConfig)
          h0' hLift

      refine ⟨m0 + m1, tape1, ?_⟩
      simpa [hsrc] using hAll

/-- On valid CNF input, checked-verifier acceptance is exactly the semantic
circuit Boolean. -/
theorem prepared_cnf_reaches_accepting_iff_eval_true
    (sigma : Assignment)
    (witness : BitString)
    (phi : Circuit)
    (hmode : modeCheck .cnf phi = true)
    (hlen : varBound phi ≤ witness.length)
    (hread :
      ∀ i, i < varBound phi →
        witness.getD i false = sigma i) :
    ∃ m tape,
      ({ state :=
           .eval (.final (evalCircuit sigma phi)),
         tape := tape } : CheckedVerifierConfig) ∈
        checkedVerifierMachine.runBranches m
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (encodeCircuit phi) }] ∧
      (checkedVerifierMachine.accepting
          (.eval (.final (evalCircuit sigma phi))) = true ↔
        evalCircuit sigma phi = true) := by
  obtain ⟨m, tape, hrun⟩ :=
    prepared_cnf_reaches_semantic_final
      sigma witness phi hmode hlen hread
  refine ⟨m, tape, hrun, ?_⟩
  change
    (checkedEvalRunLoopMachine.accepting
        (.final (evalCircuit sigma phi)) = true ↔
      evalCircuit sigma phi = true)
  rw [accepting_final]

/-- Canonical SAT-witness specialization for valid CNF circuits. -/
theorem canonical_witness_reaches_accepting_iff_eval_true
    (phi : Circuit)
    (w : SATWitness phi)
    (hcnf : isCNFBool phi = true) :
    ∃ m tape,
      ({ state :=
           .eval
             (.final
               (evalCircuit (assignmentOfWitness phi w) phi)),
         tape := tape } : CheckedVerifierConfig) ∈
        checkedVerifierMachine.runBranches m
          [{ state := checkedVerifierMachine.initial,
             tape :=
               preparedTape (witnessBits w) (encodeCircuit phi) }] ∧
      (checkedVerifierMachine.accepting
          (.eval
            (.final
              (evalCircuit (assignmentOfWitness phi w) phi))) = true ↔
        evalCircuit (assignmentOfWitness phi w) phi = true) := by
  have hmode : modeCheck .cnf phi = true := by
    simpa [modeCheck] using hcnf
  have hlen : varBound phi ≤ (witnessBits w).length := by
    simpa [witnessBits_length]
  have hread :
      ∀ i, i < varBound phi →
        (witnessBits w).getD i false =
          assignmentOfWitness phi w i := by
    intro i hi
    simp [witnessBits, assignmentOfWitness, hi]
  exact
    prepared_cnf_reaches_accepting_iff_eval_true
      (assignmentOfWitness phi w)
      (witnessBits w) phi hmode hlen hread

#print axioms MCore.Real.P01CheckedVerifierRun.checked_eval_mem_lift
#print axioms MCore.Real.P01CheckedVerifierRun.prepared_cnf_reaches_semantic_final
#print axioms MCore.Real.P01CheckedVerifierRun.prepared_cnf_reaches_accepting_iff_eval_true
#print axioms MCore.Real.P01CheckedVerifierRun.canonical_witness_reaches_accepting_iff_eval_true

end P01CheckedVerifierRun
end Real
end MCore
