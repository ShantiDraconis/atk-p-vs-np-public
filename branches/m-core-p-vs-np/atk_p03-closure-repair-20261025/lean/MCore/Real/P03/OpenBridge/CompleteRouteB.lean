import MCore.Real.P03.OpenBridge.BoundedUnique
import MCore.Real.P03.OpenBridge.UniformDecoder
import MCore.Real.P03PerfectFlipDichotomy

namespace MCore.Real.P03.OpenBridge.CompleteRouteB

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TableauDynamics
open P03UniformRangeDecoder
open P03RangeFailureFrontier
open P03PerfectFlipDichotomy

/-- Operationally explicit uniform decoder package. -/
structure UniformDecoderEffective
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  decoder : UniformRangeDecoder M hTotal
  cost : Nat → Nat
  cost_poly : PolynomialTimeBound cost

/-- Strict well-founded measure required by predecessor iteration. -/
def StrictRangeGrowth
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∀ x : BitString,
    x.length < (R_M M hTotal x).length

/-- Depth-parity certificate for the same hardened candidate M. -/
structure DepthParityCertificate
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  depth : BitString → Nat
  depthCost : Nat → Nat
  depthCost_poly : PolynomialTimeBound depthCost
  step :
    ∀ x : BitString,
      depth (R_M M hTotal x) = depth x + 1
  accepts_even :
    ∀ x : BitString,
      DeclaredAccepts M x ↔ Even (depth x)

/-- Complete material package for the constructive B branch.
PerfectFlip is not a field; it must be derived from the package. -/
structure CompleteRouteBInhabitant where
  candidate : PolyDTMCandidate
  hTotal : DeclaredClockTotal candidate
  unique : BoundedSourceUnique candidate hTotal
  decoder : UniformDecoderEffective candidate hTotal
  strictGrowth : StrictRangeGrowth candidate hTotal
  depthParity : DepthParityCertificate candidate hTotal

theorem even_succ_iff_not_even (n : Nat) :
    Even (n + 1) ↔ ¬ Even n := by
  omega

/-- The material package derives a genuine PerfectFlip. -/
theorem completeRouteB_implies_perfectFlip
    (C : CompleteRouteBInhabitant) :
    PerfectFlip C.candidate C.hTotal := by
  intro x
  rw [C.depthParity.accepts_even, C.depthParity.accepts_even]
  rw [C.depthParity.step]
  exact even_succ_iff_not_even (C.depthParity.depth x)

theorem completeRouteB_implies_existsPerfectFlip
    (C : CompleteRouteBInhabitant) :
    ExistsPerfectFlip :=
  ⟨C.candidate, C.hTotal, completeRouteB_implies_perfectFlip C⟩

theorem completeRouteB_refutes_rangeFailureLaw
    (C : CompleteRouteBInhabitant) :
    ¬ RangeFailureLaw :=
  existsPerfectFlip_iff_not_rangeFailureLaw.mp
    (completeRouteB_implies_existsPerfectFlip C)

/-- Exact current material target. No inhabitant is asserted here. -/
abbrev OpenTarget : Prop :=
  Nonempty CompleteRouteBInhabitant

#print axioms MCore.Real.P03.OpenBridge.CompleteRouteB.even_succ_iff_not_even
#print axioms MCore.Real.P03.OpenBridge.CompleteRouteB.completeRouteB_implies_perfectFlip
#print axioms MCore.Real.P03.OpenBridge.CompleteRouteB.completeRouteB_implies_existsPerfectFlip
#print axioms MCore.Real.P03.OpenBridge.CompleteRouteB.completeRouteB_refutes_rangeFailureLaw

end MCore.Real.P03.OpenBridge.CompleteRouteB
