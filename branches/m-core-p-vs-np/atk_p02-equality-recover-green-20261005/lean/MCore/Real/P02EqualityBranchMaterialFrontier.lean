import MCore.Real.P02TwoSidedExactnessAudit

namespace MCore
namespace Real
namespace P02EqualityBranchMaterialFrontier

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02TwoSidedExactnessAudit

abbrev CanonicalSAT : BitLanguage :=
  SATBits circuitBitEncoding

/-- Semantic reduction for one concrete NP realization. -/
structure SemanticReduction
    {L : BitLanguage}
    (R : PolyNTMRealization L) where
  reduce : BitString → BitString
  correct :
    ∀ x : BitString, L x ↔ CanonicalSAT (reduce x)

/-- Polynomial output-size control for one semantic reduction. -/
structure ReductionSizePolynomial
    {L : BitLanguage}
    {R : PolyNTMRealization L}
    (S : SemanticReduction R) where
  coefficient : Nat
  exponent : Nat
  length_le :
    ∀ x : BitString,
      (S.reduce x).length ≤
        coefficient * (x.length + 1) ^ exponent

/-- First genuinely operational missing atom on the equality side:
a polynomial-time DTM physically computes the reduction output. -/
structure ReductionComputationCertificate
    {L : BitLanguage}
    {R : PolyNTMRealization L}
    (S : SemanticReduction R) where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts :
    ∀ x : BitString,
      machine.HaltsWithin
        (timeBound x.length)
        (initialTMConfig machine x)
  computes :
    ∀ x : BitString,
      (machine.run
        (timeBound x.length)
        (initialTMConfig machine x)).tape =
          inputTape (S.reduce x)

/-- Full material Cook--Levin payload for one NP realization. -/
structure CookLevinMaterial
    {L : BitLanguage}
    (R : PolyNTMRealization L) where
  semantic : SemanticReduction R
  size : ReductionSizePolynomial semantic
  computation : ReductionComputationCertificate semantic

/-- Universal physical reduction producer. -/
structure UniversalCookLevinMaterializer where
  material :
    ∀ {L : BitLanguage} (R : PolyNTMRealization L),
      CookLevinMaterial R

/-- Second genuinely operational missing atom: closure of deterministic
polynomial computation under precomposition with the certified reduction. -/
structure DeterministicReductionComposition where
  lift :
    ∀ {L : BitLanguage}
      (R : PolyNTMRealization L)
      (C : CookLevinMaterial R),
      InP CanonicalSAT → InP L

/-- Equality-side material frontier: exactly the two operational atoms. -/
structure EqualityMaterialProducer where
  cookLevin : UniversalCookLevinMaterializer
  compose : DeterministicReductionComposition

def EqualityMaterialProducer.toTransfer
    (M : EqualityMaterialProducer) :
    CanonicalSATCompletenessTransfer where
  np_to_p_of_sat_in_p := by
    intro hSAT L hNP
    rcases hNP with ⟨R⟩
    exact M.compose.lift R (M.cookLevin.material R) hSAT

theorem equalityMaterialProducer_closes_p_eq_np
    (M : EqualityMaterialProducer)
    (hSAT : InP CanonicalSAT) :
    ∀ L : BitLanguage, InP L ↔ InNP L :=
  sat_in_p_implies_p_eq_np M.toTransfer hSAT

def EQUALITY_MATERIAL_OPEN_MATH : Prop :=
  Nonempty EqualityMaterialProducer

#print axioms MCore.Real.P02EqualityBranchMaterialFrontier.EqualityMaterialProducer.toTransfer
#print axioms MCore.Real.P02EqualityBranchMaterialFrontier.equalityMaterialProducer_closes_p_eq_np

end P02EqualityBranchMaterialFrontier
end Real
end MCore
