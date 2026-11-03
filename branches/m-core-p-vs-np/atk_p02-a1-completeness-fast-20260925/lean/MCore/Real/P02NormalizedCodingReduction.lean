import MCore.Real.P02CanonicalNormalization
import MCore.Real.P02G21G22Attack

namespace MCore
namespace Real
namespace P02NormalizedCodingReduction

open CanonicalFinalProof
open P02CanonicalNormalization
open P02G21G22Attack

/-- Finite-description-shaped deterministic candidate with an explicit
monomial clock.  Unlike PolyDTMCandidate it stores no arbitrary Nat → Nat
time-bound function. -/
structure NormalizedDTMDescriptor where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  accepting : Fin (stateCount + 1) → Bool
  coefficient : Nat
  exponent : Nat

def NormalizedDTMDescriptor.toCandidate
    (D : NormalizedDTMDescriptor) : PolyDTMCandidate where
  stateCount := D.stateCount
  machine := D.machine
  blank_none := D.blank_none
  accepting := D.accepting
  timeBound := canonicalTimeBound D.coefficient D.exponent
  time_poly := canonicalTimeBound_poly D.coefficient D.exponent

def descriptorOf
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat) : NormalizedDTMDescriptor where
  stateCount := M.stateCount
  machine := M.machine
  blank_none := M.blank_none
  accepting := M.accepting
  coefficient := coefficient
  exponent := exponent

@[simp] theorem descriptorOf_toCandidate
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat) :
    (descriptorOf M coefficient exponent).toCandidate =
      normalizedCandidate M coefficient exponent := by
  rfl

/-- Lower-bound target restricted to explicit monomial-clock descriptors. -/
def NormalizedG21Pointwise : Prop :=
  ∀ D : NormalizedDTMDescriptor,
    ∃ x : BitString,
      ¬ D.toCandidate.CorrectAt SATTarget x

/-- It is sufficient to diagonalize only against the explicit monomial-clock
normal forms. Every arbitrary polynomial clock admits a dominating monomial,
and correctness of the original candidate transfers to that normalization. -/
theorem normalizedG21_implies_G21
    (h : NormalizedG21Pointwise) :
    G21Pointwise := by
  intro M
  rcases M.time_poly with ⟨coefficient, exponent, hbound⟩
  let D := descriptorOf M coefficient exponent
  rcases h D with ⟨x, hbad⟩
  refine ⟨x, ?_⟩
  intro hM
  have hnorm :
      (normalizedCandidate M coefficient exponent).CorrectAt SATTarget x :=
    normalizedCandidate_correctAt
      M coefficient exponent hbound SATTarget x hM
  apply hbad
  simpa [D] using hnorm

theorem normalizedG21_implies_P02Target
    (h : NormalizedG21Pointwise) :
    P02TerminalFrontier.P02Target :=
  g21_pointwise_iff_p02_target.mp
    (normalizedG21_implies_G21 h)

#print axioms MCore.Real.P02NormalizedCodingReduction.descriptorOf_toCandidate
#print axioms MCore.Real.P02NormalizedCodingReduction.normalizedG21_implies_G21
#print axioms MCore.Real.P02NormalizedCodingReduction.normalizedG21_implies_P02Target

end P02NormalizedCodingReduction
end Real
end MCore
