import MCore.Real.P03ClosureOperations

namespace MCore
namespace Real
namespace P03ClosureOperators

open CanonicalFinalProof
open PNPNTMTableauEncoding
open P03MaterialLaw
open P03InteractionConflict
open P03TransitionSignature

theorem core_touches_iff
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (core : ClauseUnsatCore M x t)
    (block : NTMCNF) :
    CoreTouches core block ↔
      ∃ clause, clause ∈ core.clauses ∧ clause ∈ block := by
  rfl

theorem init_terminal_disjoint_operator
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (ht : 0 < t) :
    Disjoint
      (CNFVarSet (ntmInitialCNF M x t))
      (CNFVarSet (ntmFinalAcceptanceCNF M t)) :=
  init_terminal_vars_disjoint M x t ht

theorem init_terminal_sat_operator
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (ht : 0 < t)
    (hI : CNFSat (ntmInitialCNF M x t))
    (hT : CNFSat (ntmFinalAcceptanceCNF M t)) :
    CNFSat
      (ntmInitialCNF M x t ++ ntmFinalAcceptanceCNF M t) :=
  init_terminal_sat_of_both M x t ht hI hT

theorem transition_touch_operator
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (ht : 0 < t)
    (C : OrbitalInteractionConflict M x t)
    (core : ClauseUnsatCore M x t) :
    CoreTouches core (ntmTransitionsCNF M x t) :=
  interaction_conflict_core_requires_transition ht C core

theorem touch_to_occurrence_operator
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    {core : ClauseUnsatCore M x t}
    (h : CoreTouches core (ntmTransitionsCNF M x t)) :
    TransitionClauseOccurrence M x t core :=
  occurrence_of_core_touch h

#print axioms MCore.Real.P03ClosureOperators.core_touches_iff
#print axioms MCore.Real.P03ClosureOperators.init_terminal_disjoint_operator
#print axioms MCore.Real.P03ClosureOperators.init_terminal_sat_operator
#print axioms MCore.Real.P03ClosureOperators.transition_touch_operator
#print axioms MCore.Real.P03ClosureOperators.touch_to_occurrence_operator

end P03ClosureOperators
end Real
end MCore
