import MCore.Real.PNPDiscovery.OrbitCollision
import MCore.Real.P02TableauDynamics
import MCore.Real.P02OddSemanticRecurrence

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open P02ExactDiagonalFrontier
open PNPCookLevinMaterialMinCut
open P02OddSemanticRecurrence
open P02TableauDynamics

/-- The discovery reduction is definitionally the already-audited concrete
complemented Cook--Levin map. -/
theorem reductionMap_eq_R_M
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    reductionMap M hTotal = R_M M hTotal := by
  rfl

@[simp] theorem orbit_zero
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString) :
    orbit M hTotal seed 0 = seed := by
  rfl

@[simp] theorem orbit_succ
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (n : Nat) :
    orbit M hTotal seed (n + 1) =
      reductionMap M hTotal (orbit M hTotal seed n) := by
  rfl

/-- The local discovery orbit agrees pointwise with the earlier generic Orbit
instantiated by the genuine complemented Cook--Levin reducer. -/
theorem orbit_eq_genericOrbit
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString) :
    ∀ n : Nat,
      orbit M hTotal seed n =
        Orbit (R_M M hTotal) seed n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [orbit, Orbit, reductionMap_eq_R_M, ih]

/-- Exact semantic law on every edge of every discovery orbit.  This is
material CLOSED math inherited from the complemented Cook--Levin reduction. -/
theorem canonicalSAT_orbit_succ
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (n : Nat) :
    CanonicalSAT (orbit M hTotal seed (n + 1)) ↔
      ¬ DeclaredAccepts M (orbit M hTotal seed n) := by
  simpa [orbit, reductionMap] using
    (complement_reduce_correct
      M hTotal (orbit M hTotal seed n))

/-- If the material collision never occurs, two-valued logic forces every
orbit edge to flip the declared-acceptance observable. -/
theorem collisionFree_forces_flip
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (hFree : CollisionFreeOrbitRegime M hTotal)
    (seed : BitString)
    (n : Nat) :
    DeclaredAccepts M (orbit M hTotal seed (n + 1)) ↔
      ¬ DeclaredAccepts M (orbit M hTotal seed n) := by
  classical
  have hne :
      ¬ (DeclaredAccepts M (orbit M hTotal seed (n + 1)) ↔
          DeclaredAccepts M (orbit M hTotal seed n)) := by
    exact hFree seed n
  constructor
  · intro hNext hNow
    apply hne
    constructor
    · intro _
      exact hNow
    · intro _
      exact hNext
  · intro hNotNow
    by_contra hNotNext
    apply hne
    constructor
    · intro hNow
      exact False.elim (hNotNow hNow)
    · intro hNext
      exact False.elim (hNotNext hNext)

/-- In the collision-free regime the acceptance observable is exactly
two-periodic along every concrete Cook--Levin orbit. -/
theorem collisionFree_two_step_restore
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (hFree : CollisionFreeOrbitRegime M hTotal)
    (seed : BitString)
    (n : Nat) :
    DeclaredAccepts M (orbit M hTotal seed (n + 2)) ↔
      DeclaredAccepts M (orbit M hTotal seed n) := by
  exact P02OddSemanticRecurrence.two_flips_restore
    (P := fun k => DeclaredAccepts M (orbit M hTotal seed k))
    (collisionFree_forces_flip M hTotal hFree seed)
    n

/-- More generally every odd separation is observationally opposite under the
collision-free regime. -/
theorem collisionFree_odd_negates
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (hFree : CollisionFreeOrbitRegime M hTotal)
    (seed : BitString)
    (i d : Nat) :
    DeclaredAccepts M
        (orbit M hTotal seed (i + (2 * d + 1))) ↔
      ¬ DeclaredAccepts M (orbit M hTotal seed i) := by
  exact P02OddSemanticRecurrence.odd_flips_negate
    (P := fun k => DeclaredAccepts M (orbit M hTotal seed k))
    (collisionFree_forces_flip M hTotal hFree seed)
    i d

/-- Combining the real Cook--Levin semantic law with forced alternation:
on the collision-free branch SAT at the second successor agrees with the
candidate's declared acceptance two levels earlier. -/
theorem collisionFree_sat_second_succ
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (hFree : CollisionFreeOrbitRegime M hTotal)
    (seed : BitString)
    (n : Nat) :
    CanonicalSAT (orbit M hTotal seed (n + 2)) ↔
      DeclaredAccepts M (orbit M hTotal seed n) := by
  have hSat :=
    canonicalSAT_orbit_succ M hTotal seed (n + 1)
  have hFlip :=
    collisionFree_forces_flip M hTotal hFree seed n
  constructor
  · intro h
    have hNotNext :
        ¬ DeclaredAccepts M (orbit M hTotal seed (n + 1)) :=
      hSat.mp h
    by_contra hNotNow
    have hNext :
        DeclaredAccepts M (orbit M hTotal seed (n + 1)) :=
      hFlip.mpr hNotNow
    exact hNotNext hNext
  · intro hNow
    apply hSat.mpr
    intro hNext
    exact (hFlip.mp hNext) hNow

/-- Audit target: this formulation removes endpoint vocabulary, but it is
still equivalent to OrbitCollisionProducer.  It is therefore classified as
EQUIVALENT_GAP, not as mathematical progress. -/
def ObservableRecurrenceProducer : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    ∃ seed : BitString, ∃ i d : Nat,
      DeclaredAccepts M
          (orbit M hTotal seed (i + (2 * d + 1))) ↔
        DeclaredAccepts M (orbit M hTotal seed i)

/-- An odd observable recurrence is already enough to force an adjacent
collision, by the previously CLOSED parity theorem. -/
theorem observableRecurrence_to_collision
    (B : ObservableRecurrenceProducer) :
    OrbitCollisionProducer := by
  intro M hTotal
  rcases B M hTotal with ⟨seed, i, d, hRec⟩
  have hOddGeneric :
      OddSemanticRecurrence M (R_M M hTotal) := by
    refine ⟨seed, i, i + (2 * d + 1), ?_, ?_⟩
    · exact ⟨d, rfl⟩
    · have hEqOrbit := orbit_eq_genericOrbit M hTotal seed
      simpa [ObsEquiv, hEqOrbit] using hRec
  rcases oddRecurrence_implies_adjacent hOddGeneric with ⟨z, hz⟩
  refine ⟨z, 0, ?_⟩
  simpa [AcceptanceCollision, orbit, reductionMap_eq_R_M, ObsEquiv] using hz

theorem observableRecurrence_closes_exact_frontier
    (B : ObservableRecurrenceProducer) :
    TotalExactDiagonalProducer :=
  orbit_collision_producer_to_exact
    (observableRecurrence_to_collision B)

/-- Reverse audit direction: an adjacent collision is the odd recurrence with
distance one.  Hence ObservableRecurrenceProducer is only a change of language. -/
theorem collision_to_observableRecurrence
    (B : OrbitCollisionProducer) :
    ObservableRecurrenceProducer := by
  intro M hTotal
  rcases B M hTotal with ⟨seed, n, hCollision⟩
  refine ⟨seed, n, 0, ?_⟩
  simpa [AcceptanceCollision, Nat.mul_zero, Nat.zero_add] using hCollision

theorem observableRecurrence_iff_collision :
    ObservableRecurrenceProducer ↔ OrbitCollisionProducer := by
  constructor
  · exact observableRecurrence_to_collision
  · exact collision_to_observableRecurrence

#print axioms MCore.Real.PNPDiscovery.reductionMap_eq_R_M
#print axioms MCore.Real.PNPDiscovery.orbit_eq_genericOrbit
#print axioms MCore.Real.PNPDiscovery.canonicalSAT_orbit_succ
#print axioms MCore.Real.PNPDiscovery.collisionFree_forces_flip
#print axioms MCore.Real.PNPDiscovery.collisionFree_two_step_restore
#print axioms MCore.Real.PNPDiscovery.collisionFree_odd_negates
#print axioms MCore.Real.PNPDiscovery.collisionFree_sat_second_succ
#print axioms MCore.Real.PNPDiscovery.observableRecurrence_to_collision
#print axioms MCore.Real.PNPDiscovery.observableRecurrence_closes_exact_frontier
#print axioms MCore.Real.PNPDiscovery.collision_to_observableRecurrence
#print axioms MCore.Real.PNPDiscovery.observableRecurrence_iff_collision

end PNPDiscovery
end Real
end MCore
