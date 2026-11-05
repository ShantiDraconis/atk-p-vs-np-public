import P02.LANE4.StructuralClosure
import MCore.Real.P02BehavioralAlignment
import MCore.Real.P02ComplementRunRealization

namespace P02
namespace LANE4
namespace OPEN_MATH
namespace BehavioralAlignment

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.P02BehavioralAlignment
open MCore.Real.P02ComplementRunRealization
open MCore.Real.P02TotalCandidateKleeneReduction
open MCore.Real.PNPCookLevinMaterialMinCut

/-- Canonical reduction output used by the remaining semantic frontier. -/
abbrev reduceM
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) : BitString :=
  (complementSemanticReduction M hTotal).reduce x

/-- The already-closed Cook--Levin semantic fact. -/
theorem reduceM_sat_iff_not_accepts
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    CanonicalSAT (reduceM M hTotal x) ↔
      ¬ DeclaredAccepts M x := by
  simpa [reduceM] using complement_reduce_correct M hTotal x

/-- Positive behavioral branch. -/
def SameBehaviorAt
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) : Prop :=
  DeclaredAccepts M (reduceM M hTotal x) ↔
    DeclaredAccepts M x

/-- Opposite behavioral branch. -/
def OppositeBehaviorAt
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) : Prop :=
  DeclaredAccepts M (reduceM M hTotal x) ↔
    ¬ DeclaredAccepts M x

/-- For any fixed source, the two Boolean-valued acceptance propositions are
either equal or opposite.  This is propositional case analysis only; it does
not select the useful branch uniformly. -/
theorem behavior_dichotomy_at
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    SameBehaviorAt M hTotal x ∨
      OppositeBehaviorAt M hTotal x := by
  classical
  by_cases hx : DeclaredAccepts M x
  · by_cases hr : DeclaredAccepts M (reduceM M hTotal x)
    · left
      constructor <;> intro <;> assumption
    · right
      constructor
      · intro hred
        exact False.elim (hr hred)
      · intro hnotx
        exact False.elim (hnotx hx)
  · by_cases hr : DeclaredAccepts M (reduceM M hTotal x)
    · right
      constructor
      · intro _
        exact hx
      · intro _
        exact hr
    · left
      constructor
      · intro hred
        exact False.elim (hr hred)
      · intro hx'
        exact False.elim (hx hx')

theorem not_same_implies_opposite
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString)
    (hNotSame : ¬ SameBehaviorAt M hTotal x) :
    OppositeBehaviorAt M hTotal x := by
  rcases behavior_dichotomy_at M hTotal x with hSame | hOpp
  · exact False.elim (hNotSame hSame)
  · exact hOpp

theorem sameBehaviorAt_gives_behavioral_alignment
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString)
    (hSame : SameBehaviorAt M hTotal x) :
    BehavioralSelfAlignment M hTotal := by
  exact ⟨x, by simpa [SameBehaviorAt, reduceM] using hSame⟩

/-- The opposite branch does NOT give UniversalFailure.  Together with the
Cook--Levin complement identity it gives correctness of M on this specific
reduction output. -/
theorem oppositeBehaviorAt_implies_correct_on_reduction
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString)
    (hOpp : OppositeBehaviorAt M hTotal x) :
    DeclaredAccepts M (reduceM M hTotal x) ↔
      CanonicalSAT (reduceM M hTotal x) := by
  rw [hOpp]
  exact (reduceM_sat_iff_not_accepts M hTotal x).symm

/-- Exact local outcome exposed without pretending that either branch closes
the global endpoint. -/
def LocalReductionOutcome
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) : Prop :=
  SameBehaviorAt M hTotal x ∨
    (DeclaredAccepts M (reduceM M hTotal x) ↔
      CanonicalSAT (reduceM M hTotal x))

theorem local_reduction_outcome
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    LocalReductionOutcome M hTotal x := by
  rcases behavior_dichotomy_at M hTotal x with hSame | hOpp
  · exact Or.inl hSame
  · exact Or.inr
      (oppositeBehaviorAt_implies_correct_on_reduction
        M hTotal x hOpp)

/-- A clock/fuel inequality is only a resource statement. -/
def FuelDominatesSourceSimulation
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) : Prop :=
  M.timeBound (reduceM M hTotal x).length ≥
    M.timeBound x.length

/-- A machine-specific semantic transport theorem.  This is the strong
missing bridge: fuel dominance is not sufficient by itself. -/
def FuelToBehaviorBridge : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString),
    FuelDominatesSourceSimulation M hTotal x →
      SameBehaviorAt M hTotal x

/-- Witness-producing resource side of the proposed route. -/
def FuelWitnessProducer : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    ∃ x : BitString,
      FuelDominatesSourceSimulation M hTotal x

/-- Pointwise packaged witness. -/
structure FuelWitness
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  source : BitString
  dominates :
    FuelDominatesSourceSimulation M hTotal source

theorem fuelWitnessProducer_iff_packaged :
    FuelWitnessProducer ↔
      ∀ (M : PolyDTMCandidate)
        (hTotal : DeclaredClockTotal M),
        Nonempty (FuelWitness M hTotal) := by
  constructor
  · intro W M hTotal
    rcases W M hTotal with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  · intro W M hTotal
    rcases W M hTotal with ⟨w⟩
    exact ⟨w.source, w.dominates⟩

/-- If the resource witness and genuine semantic transport are both available,
the exact remaining behavioral producer follows. -/
theorem fuel_route_closes_behavioral_alignment
    (W : FuelWitnessProducer)
    (B : FuelToBehaviorBridge) :
    TotalBehavioralAlignmentProducer := by
  intro M hTotal
  rcases W M hTotal with ⟨x, hx⟩
  exact sameBehaviorAt_gives_behavioral_alignment
    M hTotal x (B M hTotal x hx)

/-- Exact material package for the proposed fuel route. -/
structure FuelRouteProducer where
  witness : FuelWitnessProducer
  bridge : FuelToBehaviorBridge

theorem fuelRouteProducer_closes_T10
    (P : FuelRouteProducer) :
    TotalBehavioralAlignmentProducer :=
  fuel_route_closes_behavioral_alignment P.witness P.bridge

/-- The structural R5 theorem is useful information, but it does not inhabit
FuelToBehaviorBridge.  This theorem records only the valid consequence:
distinct source strings have distinct reduction outputs. -/
theorem structural_reduction_injective
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    Function.Injective (reduceM M hTotal) := by
  simpa [reduceM] using
    P02.LANE4.structuralClosure.r5_complement_reduce_injective
      M hTotal

/-- If a SameBehavior witness exists, the existing repository chain produces
the exact diagonal witness. -/
theorem sameBehaviorAt_gives_exact_diagonal
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString)
    (hSame : SameBehaviorAt M hTotal x) :
    P02ExactDiagonalFrontier.ExactDiagonalWitness M := by
  apply behavioral_alignment_gives_exact_witness M hTotal
  exact sameBehaviorAt_gives_behavioral_alignment
    M hTotal x hSame

#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.reduceM_sat_iff_not_accepts
#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.behavior_dichotomy_at
#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.oppositeBehaviorAt_implies_correct_on_reduction
#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.local_reduction_outcome
#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.fuelWitnessProducer_iff_packaged
#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.fuel_route_closes_behavioral_alignment
#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.fuelRouteProducer_closes_T10
#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.structural_reduction_injective
#print axioms P02.LANE4.OPEN_MATH.BehavioralAlignment.sameBehaviorAt_gives_exact_diagonal

end BehavioralAlignment
end OPEN_MATH
end LANE4
end P02
