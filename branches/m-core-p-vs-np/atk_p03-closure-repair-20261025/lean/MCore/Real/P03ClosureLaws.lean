import MCore.Real.P03ClosureOperators

namespace MCore
namespace Real
namespace P03ClosureLaws

open CanonicalFinalProof
open P02ComplementRunRealization
open PNPNTMTableauEncoding
open P03InteractionConflict
open P03TransitionSignature

theorem interaction_exposes_transition_step
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (ht : 0 < t)
    (C : OrbitalInteractionConflict M x t)
    (core : ClauseUnsatCore M x t) :
    ∃ s, s < t ∧
      ∃ clause,
        clause ∈ core.clauses ∧
        clause ∈ ntmTransitionStepCNF M x t s := by
  let occ := occurrence_of_interaction_core ht C core
  exact
    ⟨occ.step, occ.step_lt, occ.clause,
      occ.clause_in_core, occ.clause_in_step⟩

theorem interaction_exposes_state_symbol_case
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (ht : 0 < t)
    (C : OrbitalInteractionConflict M x t)
    (core : ClauseUnsatCore M x t) :
    ∃ s, s < t ∧
      ∃ clause ∈ core.clauses,
        ∃ q : Fin (M.stateCount + 1),
          ∃ a : Option Bool,
            clause ∈ ntmTransitionCaseCNF M x t s q a := by
  let occ := occurrence_of_interaction_core ht C core
  rcases transition_step_clause_has_case occ.clause_in_step with
    ⟨q, a, hCase⟩
  exact
    ⟨occ.step, occ.step_lt, occ.clause,
      occ.clause_in_core, q, a, hCase⟩

theorem deterministic_complement_has_single_index
    (candidate : PolyDTMCandidate)
    (q : Fin (candidate.stateCount + 1))
    (a : Option Bool)
    {j1 j2 : Nat}
    {tr1 tr2 :
      Fin (candidate.stateCount + 1) × Option Bool × Direction}
    (h1 :
      (j1, tr1) ∈ ntmIndexedTransitions
        ((complementToNTMCandidate candidate).machine.transition q a))
    (h2 :
      (j2, tr2) ∈ ntmIndexedTransitions
        ((complementToNTMCandidate candidate).machine.transition q a)) :
    j1 = j2 :=
  complement_no_distinct_choice_indices candidate q a h1 h2

theorem deterministic_complement_has_single_entry
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

#print axioms MCore.Real.P03ClosureLaws.interaction_exposes_transition_step
#print axioms MCore.Real.P03ClosureLaws.interaction_exposes_state_symbol_case
#print axioms MCore.Real.P03ClosureLaws.deterministic_complement_has_single_index
#print axioms MCore.Real.P03ClosureLaws.deterministic_complement_has_single_entry

end P03ClosureLaws
end Real
end MCore
