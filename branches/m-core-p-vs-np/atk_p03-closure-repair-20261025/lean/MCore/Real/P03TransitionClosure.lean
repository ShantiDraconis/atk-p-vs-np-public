import MCore.Real.P03ClosureLaws

namespace MCore
namespace Real
namespace P03TransitionClosure

open CanonicalFinalProof
open PNPNTMTableauEncoding
open P03InteractionConflict
open P03TransitionSignature

/--
Complete structural witness extracted from a genuine interaction core:
real transition step, real clause, concrete state/head-symbol case, and its
halted-vs-active classification.
-/
structure TransitionClosureWitness
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (core : ClauseUnsatCore M x t) where
  occurrence : TransitionClauseOccurrence M x t core
  signature : TransitionInteractionSignature M x t core
  same_clause : signature.clause = occurrence.clause
  same_step : signature.step = occurrence.step

def transitionClosureWitness
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (ht : 0 < t)
    (C : OrbitalInteractionConflict M x t)
    (core : ClauseUnsatCore M x t) :
    TransitionClosureWitness M x t core := by
  let occ := occurrence_of_interaction_core ht C core
  let sig := signature_of_occurrence occ
  exact
    { occurrence := occ
      signature := sig
      same_clause := rfl
      same_step := rfl }

/--
If the classified active clause is in the effect region, the complete concrete
machine transition payload is extracted without any additional semantic
assumption.
-/
def transitionClosureEffect
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    {core : ClauseUnsatCore M x t}
    (W : TransitionClosureWitness M x t core)
    (hActive : W.signature.kind = .activeChoice)
    (hEffect :
      ∃ p ∈ ntmIndexedTransitions
          (M.machine.transition W.signature.q W.signature.a),
        W.signature.clause ∈
          ntmChoiceEffectCNF M x t W.signature.step
            W.signature.q W.signature.a p) :
    ActiveEffectSignature M x t core :=
  active_effect_signature_of_region W.signature hActive hEffect

/-- Deterministic specialization of a complemented active effect. -/
def deterministicTransitionClosure
    (candidate : PolyDTMCandidate)
    {x : BitString}
    {t : Nat}
    {core :
      ClauseUnsatCore (complementToNTMCandidate candidate) x t}
    (effect :
      ActiveEffectSignature
        (complementToNTMCandidate candidate) x t core) :
    DeterministicEffectSignature candidate x t core :=
  deterministic_effect_signature candidate effect

#print axioms MCore.Real.P03TransitionClosure.transitionClosureWitness
#print axioms MCore.Real.P03TransitionClosure.transitionClosureEffect
#print axioms MCore.Real.P03TransitionClosure.deterministicTransitionClosure

end P03TransitionClosure
end Real
end MCore
