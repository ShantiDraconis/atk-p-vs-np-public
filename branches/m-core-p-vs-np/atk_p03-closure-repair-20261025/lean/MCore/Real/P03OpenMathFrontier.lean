import MCore.Real.P03ClosureLaws
import MCore.Real.P02OddSemanticRecurrence
import MCore.Real.P02TableauDynamics

namespace MCore
namespace Real
namespace P03OpenMathFrontier

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02ComplementRunRealization
open P02TableauDynamics
open P02OddSemanticRecurrence

/-- Final control state of the full deterministic run on one complete input. -/
def FinalRunState
    (M : PolyDTMCandidate)
    (x : BitString) :
    Fin (M.stateCount + 1) :=
  (M.machine.run
    (M.timeBound x.length)
    (initialTMConfig M.machine x)).state

/-- Concrete equality of the final acceptance bits of two complete runs. -/
def FullRunAcceptEquivalent
    (M : PolyDTMCandidate)
    (u v : BitString) : Prop :=
  M.accepting (FinalRunState M u) =
    M.accepting (FinalRunState M v)

/--
Full-run acceptance equality is sufficient for the official observational
equivalence.  No local state/head proxy is used.
-/
theorem full_run_accept_equiv_implies_obs
    {M : PolyDTMCandidate}
    {u v : BitString}
    (h : FullRunAcceptEquivalent M u v) :
    ObsEquiv M u v := by
  unfold FullRunAcceptEquivalent FinalRunState at h
  unfold ObsEquiv DeclaredAccepts
  rw [h]

/--
Exact material producer still missing from the current framework.

It contains only concrete data:
* two points on one real Cook--Levin orbit,
* a genuine constructive odd gap,
* equality of the final acceptance bits of the two complete deterministic runs.

There is no ObsEquiv field.
-/
structure CrossOrbitFullInputProducer
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  seed : BitString
  i : Nat
  j : Nat
  odd : OddGap i j
  final_acceptance_equal :
    FullRunAcceptEquivalent M
      (Orbit (R_M M hTotal) seed i)
      (Orbit (R_M M hTotal) seed j)

/-- A material full-input producer immediately yields the official recurrence. -/
theorem producer_implies_odd_semantic_recurrence
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (P : CrossOrbitFullInputProducer M hTotal) :
    OddSemanticRecurrence M (R_M M hTotal) := by
  exact
    ⟨P.seed, P.i, P.j, P.odd,
      full_run_accept_equiv_implies_obs P.final_acceptance_equal⟩

/-- Universal open-math target, isolated to one exact producer family. -/
def CrossOrbitFullInputLaw : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    Nonempty (CrossOrbitFullInputProducer M hTotal)

/--
If the exact full-input law is inhabited, the previously isolated total odd
semantic recurrence follows.
-/
theorem cross_orbit_full_input_law_implies_total_odd_recurrence
    (H : CrossOrbitFullInputLaw) :
    TotalOddSemanticRecurrence := by
  intro M hTotal
  rcases H M hTotal with ⟨P⟩
  simpa [R_M] using
    (producer_implies_odd_semantic_recurrence P)

/-- Conditional transport to the already-existing universal failure theorem. -/
theorem cross_orbit_full_input_law_implies_universal_failure
    (H : CrossOrbitFullInputLaw) :
    UniversalFailure CanonicalSAT :=
  totalOddRecurrence_implies_universalFailure
    (cross_orbit_full_input_law_implies_total_odd_recurrence H)

/-- Conditional transport to the internal P≠NP endpoint already in the repo. -/
theorem cross_orbit_full_input_law_closes_internal_endpoint
    (H : CrossOrbitFullInputLaw) :
    PneqNP :=
  totalOddRecurrence_closes_internal_endpoint
    (cross_orbit_full_input_law_implies_total_odd_recurrence H)

#print axioms MCore.Real.P03OpenMathFrontier.full_run_accept_equiv_implies_obs
#print axioms MCore.Real.P03OpenMathFrontier.producer_implies_odd_semantic_recurrence
#print axioms MCore.Real.P03OpenMathFrontier.cross_orbit_full_input_law_implies_total_odd_recurrence
#print axioms MCore.Real.P03OpenMathFrontier.cross_orbit_full_input_law_implies_universal_failure
#print axioms MCore.Real.P03OpenMathFrontier.cross_orbit_full_input_law_closes_internal_endpoint

end P03OpenMathFrontier
end Real
end MCore
