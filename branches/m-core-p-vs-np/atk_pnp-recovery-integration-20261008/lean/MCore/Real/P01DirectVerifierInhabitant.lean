import MCore.Real.P01CheckedEvalReject
import MCore.Real.P01CheckedVerifierRun
import MCore.Real.P01CheckedVerifierDeterminism
import MCore.Real.P01GuessedWitnessRelation

namespace MCore
namespace Real
namespace P01DirectVerifierInhabitant

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01EvalCursorMachine
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunCircuitCertificate
open P01CheckedEvalReject
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierRun
open P01CheckedVerifierDeterminism
open P01WitnessPreservingPrep
open P01NTMRunLaws
open P01GuessedWitnessRelation

abbrev CheckedVerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

/-- The semantic assignment read directly from a concrete witness bitstring. -/
def witnessAssignment (witness : BitString) : Assignment :=
  fun i => witness.getD i false

@[simp] theorem witnessAssignment_apply
    (witness : BitString) (i : Nat) :
    witnessAssignment witness i = witness.getD i false := rfl

/--
Close the recursive rejection producer once, for every circuit and syntax mode.
This is the negative half of the direct verifier proof: no endpoint proposition,
oracle, axiom, or machine inhabitant is assumed.
-/
theorem circuit_reject_certificate
    (sigma : Assignment)
    (witness : BitString) :
    ∀ (phi : Circuit) (mode : SyntaxMode),
      CheckedCircuitRejectCertificate sigma witness mode phi := by
  intro phi
  induction phi with
  | input i =>
      intro mode
      exact input_reject_certificate sigma witness mode i
  | const v =>
      intro mode
      exact const_reject_certificate sigma witness mode v
  | not child ih =>
      intro mode
      exact not_reject_certificate sigma witness mode child
  | and left right ihLeft ihRight =>
      intro mode
      exact
        and_reject_certificate sigma witness left right
          (ihLeft .cnf) (ihRight .cnf) mode
  | or left right ihLeft ihRight =>
      intro mode
      exact
        or_reject_certificate sigma witness left right
          (ihLeft .clause) (ihRight .clause) mode

private theorem encodeCircuit_ne_nil
    (phi : Circuit) :
    encodeCircuit phi ≠ [] := by
  cases phi with
  | input i => simp [encodeCircuit]
  | const b => cases b <;> simp [encodeCircuit]
  | not c => simp [encodeCircuit]
  | and a b => simp [encodeCircuit]
  | or a b => simp [encodeCircuit]

/--
If a canonical source circuit fails the CNF grammar check, the actual checked
verifier reaches its physical reject state from the prepared witness/source
layout.
-/
theorem prepared_canonical_reaches_reject
    (witness : BitString)
    (phi : Circuit)
    (hlen : varBound phi ≤ witness.length)
    (hinvalid : modeCheck .cnf phi = false) :
    ∃ m tape,
      ({ state := .reject, tape := tape } : CheckedVerifierConfig) ∈
        checkedVerifierMachine.runBranches m
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (encodeCircuit phi) }] := by
  have hne := encodeCircuit_ne_nil phi
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
             tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
            CheckedVerifierConfig) ∈
            checkedVerifierMachine.runBranches m0
              [{ state := checkedVerifierMachine.initial,
                 tape := preparedTape witness (b :: bs) }] := h0

      obtain ⟨m1, cfg1, h1, hrej⟩ :=
        (circuit_reject_certificate
          (witnessAssignment witness) witness phi .cnf)
          hinvalid [] [] 0 0 hlen (by
            intro i hi
            rfl)

      have h1src :
          cfg1 ∈ checkedEvalRunLoopMachine.runBranches m1 [cEval] := by
        simpa [cEval, hsrc] using h1

      have hLift :=
        checked_eval_mem_lift m1 cEval cfg1 h1src

      rcases cfg1 with ⟨q, tape1⟩
      change q = .reject at hrej
      subst q

      have hLift' :
          ({ state := .reject, tape := tape1 } : CheckedVerifierConfig) ∈
            checkedVerifierMachine.runBranches m1
              [({ state := .eval checkedEvalRunLoopMachine.initial,
                  tape := evalCursorStackEndTape witness 0
                    (b :: bs) [] 0 } : CheckedVerifierConfig)] := by
        simpa [cEval, checkedEvalEmbed, P01NTMRunLaws.liftConfig] using hLift

      have hAll :=
        mem_runBranches_trans checkedVerifierMachine
          m0 m1
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (b :: bs) }]
          ({ state := .eval checkedEvalRunLoopMachine.initial,
             tape := evalCursorStackEndTape witness 0
               (b :: bs) [] 0 } : CheckedVerifierConfig)
          ({ state := .reject, tape := tape1 } : CheckedVerifierConfig)
          h0' hLift'

      refine ⟨m0 + m1, tape1, ?_⟩
      simpa [hsrc] using hAll

/--
Every canonical circuit source, with enough witness cells to cover its
variables, reaches a halted checked-verifier configuration.  This eliminates
the positive-vs-negative semantic split before the remaining uniform runtime
majorant is attached.
-/
theorem prepared_canonical_halts_exists
    (witness : BitString)
    (phi : Circuit)
    (hlen : varBound phi ≤ witness.length) :
    ∃ m,
      checkedVerifierMachine.HaltsWithin m
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (encodeCircuit phi) } := by
  cases hmode : modeCheck .cnf phi with
  | false =>
      obtain ⟨m, tape, hreach⟩ :=
        prepared_canonical_reaches_reject witness phi hlen hmode
      have hhalt :
          Halted checkedVerifierMachine
            ({ state := .reject, tape := tape } : CheckedVerifierConfig) := by
        simp [Halted, checkedVerifierMachine]
      exact ⟨m,
        haltsWithin_of_reaches_halted m
          { state := checkedVerifierMachine.initial,
            tape := preparedTape witness (encodeCircuit phi) }
          ({ state := .reject, tape := tape } : CheckedVerifierConfig)
          hreach hhalt⟩
  | true =>
      obtain ⟨m, tape, hreach⟩ :=
        prepared_cnf_reaches_semantic_final
          (witnessAssignment witness) witness phi
          hmode hlen (by
            intro i hi
            rfl)
      have hhalt :
          Halted checkedVerifierMachine
            ({ state :=
                 .eval (.final (evalCircuit (witnessAssignment witness) phi)),
               tape := tape } : CheckedVerifierConfig) := by
        unfold Halted
        cases hval : evalCircuit (witnessAssignment witness) phi <;>
          simp [checkedVerifierMachine, checkedEvalRunLoopMachine, hval]
      exact ⟨m,
        haltsWithin_of_reaches_halted m
          { state := checkedVerifierMachine.initial,
            tape := preparedTape witness (encodeCircuit phi) }
          ({ state :=
               .eval (.final (evalCircuit (witnessAssignment witness) phi)),
             tape := tape } : CheckedVerifierConfig)
          hreach hhalt⟩


/-- Canonical encoded sources reduce the bit-level verifier relation to the
CNF predicate and the concrete witness assignment. -/
theorem verifyBits_encode_iff
    (phi : Circuit)
    (witness : BitString) :
    VerifyBits (encodeCircuit phi) witness ↔
      IsCNF phi ∧
        evalCircuit (witnessAssignment witness) phi = true := by
  constructor
  · rintro ⟨psi, hdecode, hcnf, heval⟩
    rw [decodeCircuit_encode] at hdecode
    cases hdecode
    exact ⟨hcnf, by simpa [witnessAssignment] using heval⟩
  · rintro ⟨hcnf, heval⟩
    exact ⟨phi, decodeCircuit_encode phi, hcnf,
      by simpa [witnessAssignment] using heval⟩

/-- Determinism turns one reached terminal configuration into an exact
acceptance characterization at that same fuel. -/
theorem acceptsWithin_iff_of_reached_terminal
    (n : Nat)
    (start terminal : CheckedVerifierConfig)
    (hmem :
      terminal ∈ checkedVerifierMachine.runBranches n [start]) :
    checkedVerifierMachine.AcceptsWithin n start ↔
      checkedVerifierMachine.accepting terminal.state = true := by
  have heq :=
    runBranches_eq_singleton_of_mem n start terminal hmem
  unfold NTM.AcceptsWithin
  rw [heq]
  simp

/-- On every canonical circuit encoding, some concrete physical fuel already
has exact acceptance semantics.  The remaining inhabitant obligation is to
replace this existential fuel by one uniform polynomial bound and then cover
noncanonical raw bitstrings fail-closed. -/
theorem prepared_canonical_accepts_exact_exists
    (witness : BitString)
    (phi : Circuit)
    (hlen : varBound phi ≤ witness.length) :
    ∃ m,
      (checkedVerifierMachine.AcceptsWithin m
          { state := checkedVerifierMachine.initial,
            tape := preparedTape witness (encodeCircuit phi) } ↔
        VerifyBits (encodeCircuit phi) witness) := by
  cases hmode : modeCheck .cnf phi with
  | false =>
      obtain ⟨m, tape, hreach⟩ :=
        prepared_canonical_reaches_reject witness phi hlen hmode
      refine ⟨m, ?_⟩
      rw [acceptsWithin_iff_of_reached_terminal
        m
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (encodeCircuit phi) }
        ({ state := .reject, tape := tape } : CheckedVerifierConfig)
        hreach,
        verifyBits_encode_iff]
      have hnotcnf : ¬ IsCNF phi := by
        intro hcnf
        have ht := (modeCheck_cnf_iff phi).2 hcnf
        rw [hmode] at ht
        contradiction
      simp [checkedVerifierMachine, hnotcnf]
  | true =>
      obtain ⟨m, tape, hreach⟩ :=
        prepared_cnf_reaches_semantic_final
          (witnessAssignment witness) witness phi
          hmode hlen (by
            intro i hi
            rfl)
      refine ⟨m, ?_⟩
      rw [acceptsWithin_iff_of_reached_terminal
        m
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (encodeCircuit phi) }
        ({ state :=
             .eval (.final (evalCircuit (witnessAssignment witness) phi)),
           tape := tape } : CheckedVerifierConfig)
        hreach,
        verifyBits_encode_iff]
      have hcnf : IsCNF phi :=
        (modeCheck_cnf_iff phi).1 hmode
      cases hval : evalCircuit (witnessAssignment witness) phi <;>
        simp [checkedVerifierMachine, checkedEvalRunLoopMachine, hcnf, hval]

#print axioms MCore.Real.P01DirectVerifierInhabitant.circuit_reject_certificate
#print axioms MCore.Real.P01DirectVerifierInhabitant.prepared_canonical_reaches_reject
#print axioms MCore.Real.P01DirectVerifierInhabitant.prepared_canonical_halts_exists
#print axioms MCore.Real.P01DirectVerifierInhabitant.verifyBits_encode_iff
#print axioms MCore.Real.P01DirectVerifierInhabitant.acceptsWithin_iff_of_reached_terminal
#print axioms MCore.Real.P01DirectVerifierInhabitant.prepared_canonical_accepts_exact_exists

end P01DirectVerifierInhabitant
end Real
end MCore
