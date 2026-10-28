import MCore.Real.P01VerifierCircuitRun
import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace P01VerifierEvalCircuitRun

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01EvalRunLoopNTM
open P01VerifierEvalCompositeNTM
open P01VerifierCircuitRun
open P01WitnessPreservingPrep

abbrev VerifierConfig :=
  Configuration VerifierEvalState (Option Bool)

/-- Canonical witness bits agree pointwise with the semantic finite witness
below the circuit variable bound. -/
theorem witnessBits_getD_eq_assignment
    (phi : Circuit)
    (w : SATWitness phi)
    (i : Nat)
    (hi : i < varBound phi) :
    (witnessBits w).getD i false =
      assignmentOfWitness phi w i := by
  simp [witnessBits, assignmentOfWitness, hi]

/-- Reuse the already-certified eval-loop embedding. -/
theorem eval_mem_lift
    (n : Nat)
    (a b : Configuration EvalRunLoopState (Option Bool))
    (h : b ∈ evalRunLoopMachine.runBranches n [a]) :
    P01NTMRunLaws.liftConfig evalStateEmbed b ∈
      verifierEvalMachine.runBranches n
        [P01NTMRunLaws.liftConfig evalStateEmbed a] :=
  P01VerifierCircuitRun.eval_mem_lift n a b h

/-- SAT-witness specialization of the generic prepared-circuit verifier run.

No physical execution is reproved here: all tape/run content comes from
`prepared_circuit_reaches_final`. -/
theorem verifier_reaches_semantic_final
    (phi : Circuit)
    (w : SATWitness phi) :
    ∃ m tape,
      ({ state :=
           VerifierEvalState.eval
             (.final (evalCircuit (assignmentOfWitness phi w) phi)),
         tape := tape } : VerifierConfig) ∈
        verifierEvalMachine.runBranches m
          [{ state := verifierEvalMachine.initial,
             tape := preparedTape (witnessBits w) (encodeCircuit phi) }] := by
  have hlen : varBound phi ≤ (witnessBits w).length := by
    simpa [witnessBits_length]
  have hread :
      ∀ i, i < varBound phi →
        (witnessBits w).getD i false =
          assignmentOfWitness phi w i := by
    intro i hi
    exact witnessBits_getD_eq_assignment phi w i hi
  exact
    prepared_circuit_reaches_final
      (assignmentOfWitness phi w)
      (witnessBits w) phi hlen hread

/-- The terminal Boolean carried by the verifier is accepting exactly when the
semantic circuit value is true. -/
theorem verifier_reaches_accepting_iff_eval_true
    (phi : Circuit)
    (w : SATWitness phi) :
    ∃ m tape,
      ({ state :=
           VerifierEvalState.eval
             (.final (evalCircuit (assignmentOfWitness phi w) phi)),
         tape := tape } : VerifierConfig) ∈
        verifierEvalMachine.runBranches m
          [{ state := verifierEvalMachine.initial,
             tape := preparedTape (witnessBits w) (encodeCircuit phi) }] ∧
      (verifierEvalMachine.accepting
          (.eval (.final (evalCircuit (assignmentOfWitness phi w) phi))) =
            true ↔
        evalCircuit (assignmentOfWitness phi w) phi = true) := by
  obtain ⟨m, tape, hrun⟩ :=
    verifier_reaches_semantic_final phi w
  refine ⟨m, tape, hrun, ?_⟩
  change
    (evalRunLoopMachine.accepting
        (.final (evalCircuit (assignmentOfWitness phi w) phi)) = true ↔
      evalCircuit (assignmentOfWitness phi w) phi = true)
  rw [accepting_final]

#print axioms MCore.Real.P01VerifierEvalCircuitRun.witnessBits_getD_eq_assignment
#print axioms MCore.Real.P01VerifierEvalCircuitRun.eval_mem_lift
#print axioms MCore.Real.P01VerifierEvalCircuitRun.verifier_reaches_semantic_final
#print axioms MCore.Real.P01VerifierEvalCircuitRun.verifier_reaches_accepting_iff_eval_true

end P01VerifierEvalCircuitRun
end Real
end MCore
