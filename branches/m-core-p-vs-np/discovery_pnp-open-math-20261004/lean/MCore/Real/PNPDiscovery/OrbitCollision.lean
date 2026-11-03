import MCore.Real.P02BehavioralAlignment

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open P02ExactDiagonalFrontier
open P02BehavioralAlignment
open PNPCookLevinMaterialMinCut

/--
Discovery map for one total deterministic polynomial-time candidate.
It is the actual concrete complemented Cook--Levin reduction already produced
by the material lane, now treated as a dynamical map on bitstrings.
-/
def reductionMap
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    BitString → BitString :=
  (complementSemanticReduction M hTotal).reduce

/-- Forward orbit of the concrete reduction map. -/
def orbit
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString) :
    Nat → BitString
  | 0 => seed
  | n + 1 => reductionMap M hTotal (orbit M hTotal seed n)

/--
A collision is not equality of bitstrings.  It is equality of the candidate's
declared acceptance observable on two consecutive points of the real
Cook--Levin orbit.
-/
def AcceptanceCollision
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (n : Nat) : Prop :=
  DeclaredAccepts M (orbit M hTotal seed (n + 1)) ↔
    DeclaredAccepts M (orbit M hTotal seed n)

/--
One acceptance collision on the real reduction orbit already yields the exact
semantic diagonal witness.  No literal fixed point and no Kleene compiler are
used.
-/
theorem acceptance_collision_gives_exact_witness
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (n : Nat)
    (hCollision : AcceptanceCollision M hTotal seed n) :
    ExactDiagonalWitness M := by
  let x : BitString := orbit M hTotal seed n
  let y : BitString := reductionMap M hTotal x
  have hOrbit :
      orbit M hTotal seed (n + 1) = y := by
    simp [orbit, y, x]
  have hBehavior :
      DeclaredAccepts M y ↔ DeclaredAccepts M x := by
    simpa [AcceptanceCollision, x, hOrbit] using hCollision
  have hReduce :
      CanonicalSAT y ↔ ¬ DeclaredAccepts M x := by
    simpa [reductionMap, y] using
      (complement_reduce_correct M hTotal x)
  refine ⟨y, ?_⟩
  constructor
  · intro hSat hAy
    have hNotAx : ¬ DeclaredAccepts M x := hReduce.mp hSat
    exact hNotAx (hBehavior.mp hAy)
  · intro hNotAy
    apply hReduce.mpr
    intro hAx
    exact hNotAy (hBehavior.mpr hAx)

/--
Uniform material discovery target: every total polynomial-time deterministic
candidate has some concrete Cook--Levin orbit with a consecutive acceptance
collision.
-/
def OrbitCollisionProducer : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    ∃ seed : BitString, ∃ n : Nat,
      AcceptanceCollision M hTotal seed n

/--
The new orbit-collision producer is sufficient for the exact open frontier.
This theorem is transport only; it does not claim the producer is inhabited.
-/
theorem orbit_collision_producer_to_exact
    (B : OrbitCollisionProducer) :
    TotalExactDiagonalProducer := by
  intro M hTotal
  rcases B M hTotal with ⟨seed, n, hCollision⟩
  exact acceptance_collision_gives_exact_witness
    M hTotal seed n hCollision

/-- Material closure once the discovery producer is genuinely inhabited. -/
theorem orbit_collision_producer_closes_internal_endpoint
    (B : OrbitCollisionProducer) :
    PneqNP :=
  total_exact_diagonal_closes_internal_endpoint
    (orbit_collision_producer_to_exact B)

/--
Opposite discovery regime.  This is deliberately not declared impossible:
if collision production fails, the kernel must expose a candidate whose real
Cook--Levin orbit never repeats its declared acceptance value on adjacent
states.
-/
def CollisionFreeOrbitRegime
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) : Prop :=
  ∀ seed : BitString, ∀ n : Nat,
    ¬ AcceptanceCollision M hTotal seed n

/--
Exact fail-closed split for one total candidate: either the new material
collision exists, or every orbit is collision-free.  This is classical logic
only and promotes neither side to a solution.
-/
theorem collision_or_collision_free
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    (∃ seed : BitString, ∃ n : Nat,
      AcceptanceCollision M hTotal seed n) ∨
      CollisionFreeOrbitRegime M hTotal := by
  classical
  by_cases h :
      ∃ seed : BitString, ∃ n : Nat,
        AcceptanceCollision M hTotal seed n
  · exact Or.inl h
  · right
    intro seed n hCollision
    exact h ⟨seed, n, hCollision⟩

#print axioms MCore.Real.PNPDiscovery.acceptance_collision_gives_exact_witness
#print axioms MCore.Real.PNPDiscovery.orbit_collision_producer_to_exact
#print axioms MCore.Real.PNPDiscovery.orbit_collision_producer_closes_internal_endpoint
#print axioms MCore.Real.PNPDiscovery.collision_or_collision_free

end PNPDiscovery
end Real
end MCore
