import MCore.Real.P02SemanticTransformerCore

namespace MCore
namespace Real
namespace P02SemanticAlignmentCountermodel

open CanonicalFinalProof
open CanonicalCircuitBits
open P02TotalCandidateSemanticCore
open P02SemanticTransformerCore

/-- Four-state deterministic machine:
state 0 moves to the second input cell;
state 1 reads that bit;
state 2 halts/rejects;
state 3 halts/accepts.
Thus it distinguishes the canonical constant-false and constant-true tags. -/
def discriminatorMachine : TM (Fin 4) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        (1, symbol, .right)
      else if q = 1 then
        match symbol with
        | some true => (3, some true, .stay)
        | some false => (2, some false, .stay)
        | none => (2, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => (q == 2) || (q == 3) }

def discriminatorCandidate : PolyDTMCandidate :=
  { stateCount := 3
    machine := discriminatorMachine
    blank_none := rfl
    accepting := fun q => q == 3
    timeBound := fun _ => 2
    time_poly := by
      exact ⟨2, 0, by intro n; simp⟩ }

theorem discriminator_halts_two
    (x : BitString) :
    discriminatorMachine.HaltsWithin 2
      (initialTMConfig discriminatorMachine x) := by
  cases x with
  | nil =>
      rfl
  | cons b bs =>
      cases bs with
      | nil =>
          cases b <;> rfl
      | cons b₂ rest =>
          cases b <;> cases b₂ <;> rfl

theorem discriminator_clock_total :
    DeclaredClockTotal discriminatorCandidate := by
  intro x
  simpa [DeclaredHalts, discriminatorCandidate] using
    discriminator_halts_two x

theorem discriminator_rejects_constFalse :
    ¬ DeclaredAccept discriminatorCandidate
      (encodeCircuit (.const false)) := by
  intro h
  change false = true at h
  contradiction

theorem discriminator_accepts_constTrue :
    DeclaredAccept discriminatorCandidate
      (encodeCircuit (.const true)) := by
  change true = true
  rfl

/-- The semantic-negation transformer can emit only the two constant circuits.
This candidate maps those constants to their own Boolean semantics, hence the
transformed output always has the opposite declared answer from the seed. -/
theorem discriminator_no_output_alignment
    (x : BitString) :
    ¬ OutputAcceptanceAligned discriminatorCandidate x := by
  intro hAlign
  cases hbit : declaredAcceptBit discriminatorCandidate x with
  | false =>
      have htx :
          semanticNegationBits discriminatorCandidate x =
            encodeCircuit (.const true) := by
        simp [semanticNegationBits, semanticNegationCircuit, hbit]
      have hy :
          DeclaredAccept discriminatorCandidate
            (semanticNegationBits discriminatorCandidate x) := by
        rw [htx]
        exact discriminator_accepts_constTrue
      have hx : DeclaredAccept discriminatorCandidate x :=
        hAlign.mp hy
      change declaredAcceptBit discriminatorCandidate x = true at hx
      rw [hbit] at hx
      contradiction
  | true =>
      have htx :
          semanticNegationBits discriminatorCandidate x =
            encodeCircuit (.const false) := by
        simp [semanticNegationBits, semanticNegationCircuit, hbit]
      have hx : DeclaredAccept discriminatorCandidate x := by
        change declaredAcceptBit discriminatorCandidate x = true
        exact hbit
      have hy :
          DeclaredAccept discriminatorCandidate
            (semanticNegationBits discriminatorCandidate x) :=
        hAlign.mpr hx
      rw [htx] at hy
      exact discriminator_rejects_constFalse hy

/-- Formal countermodel to the proposed weakened alignment route.
The route is strictly too strong even before any P-vs-NP lower bound issue:
a total polynomial-time candidate that distinguishes the two constant tags
admits no aligned seed. -/
theorem semanticAlignmentCore_refuted :
    ¬ SemanticAlignmentCore := by
  intro H
  rcases H discriminatorCandidate discriminator_clock_total with ⟨x, hx⟩
  exact discriminator_no_output_alignment x hx

#print axioms MCore.Real.P02SemanticAlignmentCountermodel.discriminator_halts_two
#print axioms MCore.Real.P02SemanticAlignmentCountermodel.discriminator_clock_total
#print axioms MCore.Real.P02SemanticAlignmentCountermodel.discriminator_no_output_alignment
#print axioms MCore.Real.P02SemanticAlignmentCountermodel.semanticAlignmentCore_refuted

end P02SemanticAlignmentCountermodel
end Real
end MCore
