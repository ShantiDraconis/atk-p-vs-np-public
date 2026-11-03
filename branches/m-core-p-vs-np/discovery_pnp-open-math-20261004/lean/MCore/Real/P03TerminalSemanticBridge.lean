import MCore.Real.P03OpenMathFrontier

namespace MCore
namespace Real
namespace P03TerminalSemanticBridge

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02ComplementRunRealization
open P02TableauDynamics
open P02OddSemanticRecurrence
open P03OpenMathFrontier

/-- Two complete orbit inputs at a genuine odd separation. -/
structure FullInputOrbitPair
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  seed : BitString
  i : Nat
  j : Nat
  odd : OddGap i j

def FullInputOrbitPair.left
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (P : FullInputOrbitPair M hTotal) : BitString :=
  Orbit (R_M M hTotal) P.seed P.i

def FullInputOrbitPair.right
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (P : FullInputOrbitPair M hTotal) : BitString :=
  Orbit (R_M M hTotal) P.seed P.j

/-- Strongest simple run-level sufficient condition: same final control state. -/
def FullRunStateEquivalent
    (M : PolyDTMCandidate)
    (u v : BitString) : Prop :=
  FinalRunState M u = FinalRunState M v

theorem final_state_equiv_implies_accept_equiv
    {M : PolyDTMCandidate}
    {u v : BitString}
    (h : FullRunStateEquivalent M u v) :
    FullRunAcceptEquivalent M u v := by
  unfold FullRunStateEquivalent FullRunAcceptEquivalent
  rw [h]

/--
The run-level Boolean equality used by the material producer is exactly the
official ObsEquiv proposition.  This closes the semantic transport itself;
what remains open is producing such an odd-separated pair for every candidate.
-/
theorem full_run_accept_equiv_iff_obs
    {M : PolyDTMCandidate}
    {u v : BitString} :
    FullRunAcceptEquivalent M u v ↔ ObsEquiv M u v := by
  unfold FullRunAcceptEquivalent FinalRunState ObsEquiv DeclaredAccepts
  let bu :=
    M.accepting
      (M.machine.run
        (M.timeBound u.length)
        (initialTMConfig M.machine u)).state
  let bv :=
    M.accepting
      (M.machine.run
        (M.timeBound v.length)
        (initialTMConfig M.machine v)).state
  change bu = bv ↔ (bu = true ↔ bv = true)
  cases hbu : bu <;> cases hbv : bv <;> simp

/-- A material terminal witness consists of an odd-separated full-input pair
plus equality of the complete-run acceptance bits. -/
structure FullRunAcceptanceWitness
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  pair : FullInputOrbitPair M hTotal
  acceptance :
    FullRunAcceptEquivalent M pair.left pair.right

/-- Exact conversion to the frontier producer. -/
def FullRunAcceptanceWitness.toProducer
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (W : FullRunAcceptanceWitness M hTotal) :
    CrossOrbitFullInputProducer M hTotal :=
  { seed := W.pair.seed
    i := W.pair.i
    j := W.pair.j
    odd := W.pair.odd
    final_acceptance_equal := W.acceptance }

/-- Exact conversion from the frontier producer. -/
def FullRunAcceptanceWitness.ofProducer
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (P : CrossOrbitFullInputProducer M hTotal) :
    FullRunAcceptanceWitness M hTotal :=
  { pair :=
      { seed := P.seed
        i := P.i
        j := P.j
        odd := P.odd }
    acceptance := P.final_acceptance_equal }

/-- The exploded terminal witness is definitionally equivalent in content to
the existing frontier producer. -/
theorem full_run_witness_implies_odd_semantic_recurrence
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (W : FullRunAcceptanceWitness M hTotal) :
    OddSemanticRecurrence M (R_M M hTotal) :=
  producer_implies_odd_semantic_recurrence W.toProducer

/-- Exact remaining producer family after all semantic transport is closed. -/
def FullRunAcceptanceLaw : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    Nonempty (FullRunAcceptanceWitness M hTotal)

theorem full_run_acceptance_law_iff_cross_orbit_law :
    FullRunAcceptanceLaw ↔ CrossOrbitFullInputLaw := by
  constructor
  · intro H M hTotal
    rcases H M hTotal with ⟨W⟩
    exact ⟨W.toProducer⟩
  · intro H M hTotal
    rcases H M hTotal with ⟨P⟩
    exact ⟨FullRunAcceptanceWitness.ofProducer P⟩

theorem full_run_acceptance_law_implies_total_odd_recurrence
    (H : FullRunAcceptanceLaw) :
    TotalOddSemanticRecurrence := by
  apply cross_orbit_full_input_law_implies_total_odd_recurrence
  exact full_run_acceptance_law_iff_cross_orbit_law.mp H

#print axioms MCore.Real.P03TerminalSemanticBridge.final_state_equiv_implies_accept_equiv
#print axioms MCore.Real.P03TerminalSemanticBridge.full_run_accept_equiv_iff_obs
#print axioms MCore.Real.P03TerminalSemanticBridge.full_run_witness_implies_odd_semantic_recurrence
#print axioms MCore.Real.P03TerminalSemanticBridge.full_run_acceptance_law_iff_cross_orbit_law
#print axioms MCore.Real.P03TerminalSemanticBridge.full_run_acceptance_law_implies_total_odd_recurrence

end P03TerminalSemanticBridge
end Real
end MCore
