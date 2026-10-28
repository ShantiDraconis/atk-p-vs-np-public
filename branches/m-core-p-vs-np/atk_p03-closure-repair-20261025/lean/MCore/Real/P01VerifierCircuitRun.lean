import MCore.Real.P01VerifierEvalCompositeNTM
import MCore.Real.P01EvalRunCircuitCertificate

namespace MCore
namespace Real
namespace P01VerifierCircuitRun

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01NTMRunLaws
open P01WitnessPreservingPrep
open P01EvalCursorMachine
open P01EvalRunLoopNTM
open P01EvalRunCircuitCertificate
open P01VerifierEvalCompositeNTM

abbrev VerifierConfig :=
  Configuration VerifierEvalState (Option Bool)

def liftEvalConfig
    (c : Configuration EvalRunLoopState (Option Bool)) :
    VerifierConfig :=
  P01NTMRunLaws.liftConfig evalStateEmbed c

/-- Membership transport for an already-certified evalRun execution into the
prepared-input verifier core. -/
theorem eval_mem_lift
    (n : Nat)
    (a b : Configuration EvalRunLoopState (Option Bool))
    (h : b ∈ evalRunLoopMachine.runBranches n [a]) :
    liftEvalConfig b ∈
      verifierEvalMachine.runBranches n [liftEvalConfig a] := by
  rw [show [liftEvalConfig a] =
      [a].map (P01NTMRunLaws.liftConfig evalStateEmbed) by rfl]
  rw [eval_runBranches_map]
  exact List.mem_map.mpr ⟨b, h, rfl⟩

/-- Physical semantic closure for one canonical circuit.

Starting directly from the witness-preparation handoff layout
`preparedTape witness (encodeCircuit phi)`, the single verifier core reaches
the exact Boolean value of `phi`.  This theorem intentionally carries no
runtime majorant yet; it closes the layout + physical-run + semantic layer
before the polynomial budget is attached. -/
theorem prepared_circuit_reaches_final
    (sigma : Assignment)
    (witness : BitString)
    (phi : CircuitK1.Circuit)
    (hlen : varBound phi ≤ witness.length)
    (hread :
      ∀ i, i < varBound phi →
        witness.getD i false = sigma i) :
    ∃ m tape,
      ({ state := .eval (.final (evalCircuit sigma phi)),
         tape := tape } : VerifierConfig) ∈
        verifierEvalMachine.runBranches m
          [{ state := verifierEvalMachine.initial,
             tape := preparedTape witness (encodeCircuit phi) }] := by
  have hne := encodeCircuit_ne_nil phi
  cases hsrc : encodeCircuit phi with
  | nil =>
      exact False.elim (hne hsrc)
  | cons b bs =>
      obtain ⟨mEntry, hmEntry, hEntry⟩ :=
        prepared_nonempty_reaches_eval_start witness b bs

      let cLoop0 : Configuration EvalRunLoopState (Option Bool) :=
        { state := evalRunLoopMachine.initial,
          tape :=
            evalCursorStackEndTape witness 0
              (encodeCircuit phi) [] 0 }
      let cVerifierLoop0 : VerifierConfig :=
        liftEvalConfig cLoop0

      have hEntry' :
          cVerifierLoop0 ∈
            verifierEvalMachine.runBranches mEntry
              [{ state := verifierEvalMachine.initial,
                 tape := preparedTape witness (encodeCircuit phi) }] := by
        simpa [cVerifierLoop0, cLoop0, liftEvalConfig, evalStateEmbed, hsrc]
          using hEntry

      obtain ⟨mEval, cfg, hEval, hout⟩ :=
        (circuit_certificate sigma witness phi)
          [] [] 0 0 hlen hread

      have hEvalLift :
          liftEvalConfig cfg ∈
            verifierEvalMachine.runBranches mEval [cVerifierLoop0] := by
        apply eval_mem_lift
        simpa [cLoop0] using hEval

      have hAll :=
        mem_runBranches_trans verifierEvalMachine
          mEntry mEval
          [{ state := verifierEvalMachine.initial,
             tape := preparedTape witness (encodeCircuit phi) }]
          cVerifierLoop0 (liftEvalConfig cfg)
          hEntry' hEvalLift

      have hout' :
          ∃ tape : Tape (Option Bool),
            cfg =
              { state := EvalRunLoopState.final (evalCircuit sigma phi),
                tape := tape } := by
        simpa [LoopOutcome] using hout
      rcases hout' with ⟨tape, rfl⟩
      refine ⟨mEntry + mEval, tape, ?_⟩
      simpa [hsrc, liftEvalConfig, evalStateEmbed] using hAll

#print axioms MCore.Real.P01VerifierCircuitRun.eval_mem_lift
#print axioms MCore.Real.P01VerifierCircuitRun.prepared_circuit_reaches_final

end P01VerifierCircuitRun
end Real
end MCore
