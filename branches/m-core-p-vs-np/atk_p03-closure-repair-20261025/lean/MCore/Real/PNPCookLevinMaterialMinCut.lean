
import MCore.Real.PNPEqualityBranchMinCut

namespace MCore
namespace Real
namespace PNPCookLevinMaterialMinCut

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open PNPEqualityBranchMinCut

abbrev CanonicalSAT : BitLanguage :=
  SATBits circuitBitEncoding

/--
Semantic Cook--Levin reduction payload for one concrete NP realization.
It contains no P=NP or NP subset P field.
-/
structure NTMToCanonicalSATSemanticReduction
    {L : BitLanguage}
    (R : PolyNTMRealization L) where
  reduce : BitString -> BitString
  correct :
    forall x : BitString,
      L x <-> CanonicalSAT (reduce x)

/--
Quantitative size control for the generated SAT instance.
-/
structure ReductionSizePolynomial
    {L : BitLanguage}
    {R : PolyNTMRealization L}
    (S : NTMToCanonicalSATSemanticReduction R) where
  coefficient : Nat
  exponent : Nat
  length_le :
    forall x : BitString,
      (S.reduce x).length <=
        coefficient * (x.length + 1) ^ exponent

/--
Operational reduction producer. The physical computation relation remains
visible instead of being hidden inside the endpoint.
-/
structure ReductionComputationCertificate
    {L : BitLanguage}
    {R : PolyNTMRealization L}
    (S : NTMToCanonicalSATSemanticReduction R) where
  stateCount : Nat
  machine : TM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts :
    forall x : BitString,
      machine.HaltsWithin
        (timeBound x.length)
        (initialTMConfig machine x)
  computes :
    forall x : BitString,
      (machine.run
        (timeBound x.length)
        (initialTMConfig machine x)).tape =
          inputTape (S.reduce x)

/--
Exact Cook--Levin material package for one NP realization.
-/
structure CanonicalCookLevinMaterial
    {L : BitLanguage}
    (R : PolyNTMRealization L) where
  semantic : NTMToCanonicalSATSemanticReduction R
  size : ReductionSizePolynomial semantic
  computation : ReductionComputationCertificate semantic

/--
Universal Cook--Levin materializer for the canonical NP machine model.
-/
structure UniversalCanonicalCookLevinMaterializer where
  material :
    forall {L : BitLanguage} (R : PolyNTMRealization L),
      CanonicalCookLevinMaterial R

/--
Independent deterministic composition producer. It contains only closure
under precomposition with the certified reduction, not the final equality.
-/
structure DeterministicReductionComposition where
  lift :
    forall {L : BitLanguage}
      (R : PolyNTMRealization L)
      (C : CanonicalCookLevinMaterial R),
      InP CanonicalSAT -> InP L

/--
The two exact producer atoms for the equality branch.
-/
structure CanonicalSATCompletenessMaterializer where
  cookLevin : UniversalCanonicalCookLevinMaterializer
  compose : DeterministicReductionComposition

def CanonicalSATCompletenessMaterializer.toTransfer
    (M : CanonicalSATCompletenessMaterializer) :
    CanonicalSATCompletenessTransfer where
  np_to_p_of_sat_in_p := by
    intro hSAT L hNP
    rcases hNP with ⟨R⟩
    exact M.compose.lift R (M.cookLevin.material R) hSAT

theorem materializer_closes_equality_branch
    (M : CanonicalSATCompletenessMaterializer)
    (hSAT : InP CanonicalSAT)
    (hPsubNP : forall L : BitLanguage, InP L -> InNP L) :
    forall L : BitLanguage, InP L <-> InNP L :=
  sat_in_p_closes_equality M.toTransfer hSAT hPsubNP

def PNP_COOK_LEVIN_OPEN_MATH : Prop :=
  Nonempty CanonicalSATCompletenessMaterializer

#print axioms MCore.Real.PNPCookLevinMaterialMinCut.CanonicalSATCompletenessMaterializer.toTransfer
#print axioms MCore.Real.PNPCookLevinMaterialMinCut.materializer_closes_equality_branch

end PNPCookLevinMaterialMinCut
end Real
end MCore
