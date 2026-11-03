import MCore.Real.P03MaterialLaw
import MCore.Real.SourceRecovery

namespace MCore
namespace Real
namespace P03Lemmas

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02ComplementRunRealization
open P02TableauDynamics
open P02OddSemanticRecurrence
open P03MaterialLaw
open SourceRecovery

/--
Every concrete orbit step retains and decodes its immediate predecessor.

This is the non-prefix recovery law needed by P03: it uses the actual
ntmInitialCNF/source decoder and makes no claim that the predecessor is a
literal bit-prefix of the successor.
-/
@[simp] theorem decode_recovers_orbit_step
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (k : Nat) :
    decodeSourceBits
        (complementToNTMCandidate M)
        (Orbit (R_M M hTotal) seed k).length
        (M.timeBound (Orbit (R_M M hTotal) seed k).length)
        (Orbit (R_M M hTotal) seed (k + 1)) =
      some (Orbit (R_M M hTotal) seed k) := by
  simpa [Orbit, R_M] using
    (SourceRecovery.decodeSource_reduce
      M hTotal (Orbit (R_M M hTotal) seed k))

/--
The canonical full-support conflict witness necessarily includes the transition
block.  This is a structural fact about fullSupport only; it does not claim
that every minimal or relevant conflict must contain Transit.
-/
theorem full_conflict_support_contains_transition
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (hUnsat : CNFUnsat (boundedExecTableauCNF_NTM M x t)) :
    (((fullConflictExtractor M).locate x t hUnsat).support.transit = true) := by
  rfl

/-- Support containing exactly the initial and transition blocks. -/
def initTransitSupport : ClauseConflictSupport where
  init := true
  transit := true
  terminal := false
  nonempty := Or.inl rfl

@[simp] theorem supportedCNF_initTransitSupport
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    supportedCNF initTransitSupport M x t =
      ntmInitialCNF M x t ++ ntmTransitionsCNF M x t := by
  rfl

/--
Any genuine tableau path gives one assignment satisfying Init and Transit
simultaneously.  Acceptance is not used.
-/
theorem init_transit_sat_of_path
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (path : Fin (t + 1) → NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path) :
    CNFSat (supportedCNF initTransitSupport M x t) := by
  refine ⟨pathAssignment M x t path hPath, ?_⟩
  rw [supportedCNF_initTransitSupport]
  exact (evalNTMCNF_append
    (pathAssignment M x t path hPath)
    (ntmInitialCNF M x t)
    (ntmTransitionsCNF M x t)).2
      ⟨pathAssignment_initial_sat M x t path hPath,
       pathAssignment_transitions_sat M x t path hPath⟩

/--
Therefore a support consisting only of Init+Transit cannot be an UNSAT
conflict whenever it corresponds to a real tableau path.
-/
theorem init_transit_not_unsat_of_path
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (path : Fin (t + 1) → NTMConfig M)
    (hPath : NTMTableauPath M t (initialNTMConfig M.machine x) path) :
    ¬ CNFUnsat (supportedCNF initTransitSupport M x t) := by
  intro hUnsat
  rcases init_transit_sat_of_path M x t path hPath with ⟨sigma, hSat⟩
  have hFalse := hUnsat sigma
  rw [hSat] at hFalse
  contradiction

#print axioms MCore.Real.P03Lemmas.decode_recovers_orbit_step
#print axioms MCore.Real.P03Lemmas.full_conflict_support_contains_transition
#print axioms MCore.Real.P03Lemmas.init_transit_sat_of_path
#print axioms MCore.Real.P03Lemmas.init_transit_not_unsat_of_path

end P03Lemmas
end Real
end MCore
