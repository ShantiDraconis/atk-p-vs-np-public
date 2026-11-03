import MCore.Real.P03ClosureClasses
import MCore.Real.P03Lemmas

namespace MCore
namespace Real
namespace P03ClosureOperations

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02ComplementRunRealization
open P02TableauDynamics
open P02OddSemanticRecurrence
open PNPNTMTableauEncoding
open P03MaterialLaw
open P03Lemmas
open P03InteractionConflict
open P03TransitionSignature

theorem eval_append_true_iff
    (sigma : Assignment)
    (F G : NTMCNF) :
    evalNTMCNF sigma (F ++ G) = true ↔
      evalNTMCNF sigma F = true ∧ evalNTMCNF sigma G = true :=
  evalNTMCNF_append sigma F G

theorem sat_restricts_to_clause_subset
    {small big : NTMCNF}
    (hSub : ∀ clause ∈ small, clause ∈ big)
    (hSat : CNFSat big) :
    CNFSat small := by
  rcases hSat with ⟨sigma, hBig⟩
  exact ⟨sigma, cnf_sat_of_clause_subset hBig hSub⟩

theorem unsat_extends_to_clause_superset
    {small big : NTMCNF}
    (hUnsat : CNFUnsat small)
    (hSub : ∀ clause ∈ small, clause ∈ big) :
    CNFUnsat big :=
  cnf_unsat_of_unsat_subset hUnsat hSub

theorem decode_outer_orbit_step
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (k : Nat) :
    decodeSourceBits
        (complementToNTMCandidate M)
        (Orbit (R_M M hTotal) seed k).length
        (M.timeBound (Orbit (R_M M hTotal) seed k).length)
        (Orbit (R_M M hTotal) seed (k + 1)) =
      some (Orbit (R_M M hTotal) seed k) :=
  decode_recovers_orbit_step M hTotal seed k

theorem deterministic_complement_entry_unique
    (candidate : PolyDTMCandidate)
    (q : Fin (candidate.stateCount + 1))
    (a : Option Bool)
    {p1 p2 :
      Nat × (Fin (candidate.stateCount + 1) × Option Bool × Direction)}
    (h1 :
      p1 ∈ ntmIndexedTransitions
        ((complementToNTMCandidate candidate).machine.transition q a))
    (h2 :
      p2 ∈ ntmIndexedTransitions
        ((complementToNTMCandidate candidate).machine.transition q a)) :
    p1 = p2 :=
  complement_indexed_entry_unique candidate q a h1 h2

#print axioms MCore.Real.P03ClosureOperations.eval_append_true_iff
#print axioms MCore.Real.P03ClosureOperations.sat_restricts_to_clause_subset
#print axioms MCore.Real.P03ClosureOperations.unsat_extends_to_clause_superset
#print axioms MCore.Real.P03ClosureOperations.decode_outer_orbit_step
#print axioms MCore.Real.P03ClosureOperations.deterministic_complement_entry_unique

end P03ClosureOperations
end Real
end MCore
