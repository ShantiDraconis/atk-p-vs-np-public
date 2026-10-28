import MCore.Real.P01WitnessPrepGlobal
import MCore.Real.P01GuessedWitnessRelation

namespace MCore
namespace Real
namespace P01VerifierDecomposition

/-!
# P01 verifier = decode/normalize phase ; evaluation phase

`P01WitnessPrepGlobal.p01_of_verifier` reduced `P01ConstructionGap` to one
concrete `P01VerifierPhase prepPhase.layout`.  This module splits that object
into two smaller machine specifications and proves, with the existing `seq`
run laws, that they compose into a verifier phase:

* `P01DecodePhase layout`: from `layout bs w` it halts within a polynomial
  bound; its accepting branches occur exactly when `bs` decodes to a CNF
  circuit, and they hand off one normalized tape `outLayout bs w`;
* `P01EvalPhase outLayout`: from `outLayout bs w` (for sources that decode to
  a CNF) it halts within a polynomial bound and accepts iff the decoded CNF
  evaluates to `true` under the guessed bits.

`verifierPhase D E : P01VerifierPhase layout` and
`p01_of_decode_and_eval D E : P01ConstructionGap` follow.  Nothing here
constructs `D` or `E`; they are the remaining machine-level obligations.
No axiom, proof placeholder or endpoint hypothesis is introduced.
-/

open CircuitK1
open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open CanonicalSATWitness
open P01NTMRunLaws P01NTMPhaseSeq P01NTMSeqRun
open P01GuessedWitnessRelation P01IntegratedAssembly

/-- The source decodes to a CNF circuit. -/
def DecodesToCNF (bs : BitString) : Prop :=
  ∃ φ : Circuit, decodeCircuit bs = some φ ∧ IsCNF φ

/-- Decode/normalize phase. -/
structure P01DecodePhase (layout : BitString → BitString → Tape (Option Bool)) where
  stateCount : Nat
  machine : NTM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  disjoint : ∀ q, machine.accepting q = true → machine.rejecting q = false
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  outLayout : BitString → BitString → Tape (Option Bool)
  halts : ∀ bs w : BitString, w.length = bs.length →
    machine.HaltsWithin (timeBound bs.length) ⟨machine.initial, layout bs w⟩
  sound : ∀ bs w : BitString, w.length = bs.length →
    ∀ d ∈ machine.runBranches (timeBound bs.length) [⟨machine.initial, layout bs w⟩],
      machine.accepting d.state = true → DecodesToCNF bs ∧ d.tape = outLayout bs w
  complete : ∀ bs w : BitString, w.length = bs.length → DecodesToCNF bs →
    ∃ d ∈ machine.runBranches (timeBound bs.length) [⟨machine.initial, layout bs w⟩],
      machine.accepting d.state = true ∧ d.tape = outLayout bs w

/-- Evaluation phase on the normalized tape. -/
structure P01EvalPhase (outLayout : BitString → BitString → Tape (Option Bool)) where
  stateCount : Nat
  machine : NTM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts : ∀ bs w : BitString, w.length = bs.length → DecodesToCNF bs →
    machine.HaltsWithin (timeBound bs.length) ⟨machine.initial, outLayout bs w⟩
  correct : ∀ (bs w : BitString) (φ : Circuit), w.length = bs.length →
    decodeCircuit bs = some φ → IsCNF φ →
    (machine.AcceptsWithin (timeBound bs.length) ⟨machine.initial, outLayout bs w⟩ ↔
      evalCircuit (fun i => w.getD i false) φ = true)

section Assembly

variable {layout : BitString → BitString → Tape (Option Bool)}
variable (D : P01DecodePhase layout) (E : P01EvalPhase D.outLayout)

def verifierMachine :
    NTM (Fin (D.stateCount + E.stateCount + 1 + 1)) (Option Bool) :=
  relabel (seq D.machine E.machine) (sumToFin D.stateCount E.stateCount)
    (finToSum D.stateCount E.stateCount)

def verifierTime : TimeBound :=
  fun n => D.timeBound n + 1 + E.timeBound n

theorem hblankDE : D.machine.blank = E.machine.blank := by
  rw [D.blank_none, E.blank_none]

theorem start_eq (bs w : BitString) :
    (⟨(verifierMachine D E).initial, layout bs w⟩ :
        Configuration (Fin (D.stateCount + E.stateCount + 1 + 1)) (Option Bool)) =
      liftConfig (sumToFin D.stateCount E.stateCount)
        (L D.machine E.machine ⟨D.machine.initial, layout bs w⟩) := rfl

theorem eval_halts_on_handoffs (bs w : BitString) (hw : w.length = bs.length) :
    ∀ d ∈ D.machine.runBranches (D.timeBound bs.length) [⟨D.machine.initial, layout bs w⟩],
      D.machine.accepting d.state = true →
      E.machine.HaltsWithin (E.timeBound bs.length) (handoff D.machine E.machine d) := by
  intro d hd hacc
  rcases D.sound bs w hw d hd hacc with ⟨hcnf, htape⟩
  have := E.halts bs w hw hcnf
  simpa [handoff, htape] using this

theorem verifier_halts (bs w : BitString) (hw : w.length = bs.length) :
    (verifierMachine D E).HaltsWithin (verifierTime D E bs.length)
      ⟨(verifierMachine D E).initial, layout bs w⟩ := by
  rw [start_eq, verifierMachine, relabel_haltsWithin_iff _ _ _ (finToSum_sumToFin _ _)]
  exact seq_haltsWithin D.machine E.machine (hblankDE D E) D.disjoint
    (E.timeBound bs.length) (D.timeBound bs.length) _ (D.halts bs w hw)
    (eval_halts_on_handoffs D E bs w hw)

theorem verifier_correct (bs w : BitString) (hw : w.length = bs.length) :
    (verifierMachine D E).AcceptsWithin (verifierTime D E bs.length)
        ⟨(verifierMachine D E).initial, layout bs w⟩ ↔ VerifyBits bs w := by
  rw [start_eq, verifierMachine, relabel_acceptsWithin_iff _ _ _ (finToSum_sumToFin _ _),
    verifierTime,
    seq_acceptsWithin_iff D.machine E.machine (hblankDE D E) D.disjoint
      (D.timeBound bs.length) (E.timeBound bs.length) _ (D.halts bs w hw)
      (eval_halts_on_handoffs D E bs w hw)]
  constructor
  · rintro ⟨d, hd, hacc, hE⟩
    rcases D.sound bs w hw d hd hacc with ⟨⟨φ, hdec, hcnf⟩, htape⟩
    have hE' : E.machine.AcceptsWithin (E.timeBound bs.length)
        ⟨E.machine.initial, D.outLayout bs w⟩ := by
      simpa [handoff, htape] using hE
    exact ⟨φ, hdec, hcnf, (E.correct bs w φ hw hdec hcnf).1 hE'⟩
  · rintro ⟨φ, hdec, hcnf, heval⟩
    rcases D.complete bs w hw ⟨φ, hdec, hcnf⟩ with ⟨d, hd, hacc, htape⟩
    refine ⟨d, hd, hacc, ?_⟩
    have := (E.correct bs w φ hw hdec hcnf).2 heval
    simpa [handoff, htape] using this

/-- The verifier phase assembled from the two sub-phases. -/
def verifierPhase : P01VerifierPhase layout where
  stateCount := D.stateCount + E.stateCount + 1
  machine := verifierMachine D E
  blank_none := by
    show (seq D.machine E.machine).blank = none
    exact D.blank_none
  timeBound := verifierTime D E
  time_poly := poly_seq _ _ D.time_poly E.time_poly
  halts := verifier_halts D E
  correct := verifier_correct D E

end Assembly

/-- With the recovered prep phase, `P01ConstructionGap` reduces to one decode
phase and one evaluation phase over the prepared layout. -/
theorem p01_of_decode_and_eval
    (D : P01DecodePhase P01WitnessPrepGlobal.prepPhase.layout)
    (E : P01EvalPhase D.outLayout) :
    P01FinalCertificate.P01ConstructionGap :=
  P01WitnessPrepGlobal.p01_of_verifier (verifierPhase D E)

#print axioms verifier_halts
#print axioms verifier_correct
#print axioms verifierPhase
#print axioms p01_of_decode_and_eval

end P01VerifierDecomposition
end Real
end MCore
