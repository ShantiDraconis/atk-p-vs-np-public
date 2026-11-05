import MCore.Real.P02TerminalFrontier

namespace MCore
namespace Real
namespace P02G21G22Attack

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open FailProofAllGaps
open P02TerminalFrontier

/-- The fixed canonical SAT bit-language used by the P02 frontier. -/
abbrev SATTarget : BitLanguage :=
  SATBits circuitBitEncoding

/-- G2.1 in its minimal pointwise form: every deterministic polynomial-time
candidate has a concrete input on which it fails for the canonical SAT target.
This is the exact OPEN_MATH producer; no stronger diagonalization syntax is
silently assumed here. -/
def G21Pointwise : Prop :=
  ∀ candidate : PolyDTMCandidate,
    ∃ x : BitString,
      ¬ candidate.CorrectAt SATTarget x

/-- G2.2 is the contradiction consumer: no purported total P-realization of
the canonical SAT target can coexist with G2.1. -/
def G22Contradiction : Prop :=
  ∀ realization : PolyDTMRealization SATTarget, False

/-- The pointwise G2.1 statement is exactly the already-pinned P02 target. -/
theorem g21_pointwise_iff_p02_target :
    G21Pointwise ↔ P02Target := by
  simpa [G21Pointwise, P02Target, SATTarget, SATFailGap] using
    (failure_generator_iff_universal_failure
      (language := SATBits circuitBitEncoding)).symm

/-- G2.2 is exactly non-membership of the canonical SAT target in the
hardened deterministic class. -/
theorem g22_contradiction_iff_not_in_p :
    G22Contradiction ↔ ¬ InP SATTarget := by
  constructor
  · intro h hP
    rcases hP with ⟨realization⟩
    exact h realization
  · intro h realization
    exact h ⟨realization⟩

/-- Once G2.1 is supplied, G2.2 closes with no additional mathematical
assumption. -/
theorem g21_implies_g22
    (hG21 : G21Pointwise) :
    G22Contradiction := by
  apply g22_contradiction_iff_not_in_p.mpr
  exact p02_target_iff_sat_not_in_p.mp
    (g21_pointwise_iff_p02_target.mp hG21)

/-- Conversely, a completed G2.2 contradiction already contains the exact
G2.1 lower-bound content. Thus G2.2 is not an independent terminal producer. -/
theorem g22_implies_g21
    (hG22 : G22Contradiction) :
    G21Pointwise := by
  apply g21_pointwise_iff_p02_target.mpr
  apply p02_target_iff_sat_not_in_p.mpr
  exact g22_contradiction_iff_not_in_p.mp hG22

theorem g21_iff_g22 :
    G21Pointwise ↔ G22Contradiction :=
  ⟨g21_implies_g22, g22_implies_g21⟩

/-- P01 plus the exact G2.1 producer closes the internal separation. -/
theorem p01_g21_closes_internal
    (hP01 : SATInNPGap circuitBitEncoding)
    (hG21 : G21Pointwise) :
    PneqNP := by
  exact p01_p02_close_internal_separation
    hP01
    (g21_pointwise_iff_p02_target.mp hG21)

#print axioms MCore.Real.P02G21G22Attack.g21_pointwise_iff_p02_target
#print axioms MCore.Real.P02G21G22Attack.g22_contradiction_iff_not_in_p
#print axioms MCore.Real.P02G21G22Attack.g21_implies_g22
#print axioms MCore.Real.P02G21G22Attack.g22_implies_g21
#print axioms MCore.Real.P02G21G22Attack.g21_iff_g22
#print axioms MCore.Real.P02G21G22Attack.p01_g21_closes_internal

end P02G21G22Attack
end Real
end MCore
