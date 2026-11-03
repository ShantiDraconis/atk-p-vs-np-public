import MCore.Real.P03InteractionConflict

namespace MCore
namespace Real
namespace P03TransitionSignature

open CanonicalFinalProof
open PNPNTMTableauEncoding
open P03MaterialLaw
open P03InteractionConflict

/--
A concrete transition-clause occurrence together with the real tableau step
from which that clause originates.
-/
structure TransitionClauseOccurrence
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (core : ClauseUnsatCore M x t) where
  step : Nat
  step_lt : step < t
  clause : NTMClause
  clause_in_core : clause ∈ core.clauses
  clause_in_step :
    clause ∈ ntmTransitionStepCNF M x t step

/--
Membership in the flattened transition CNF exposes the genuine time step.
No arithmetic decoding of variable numbers is used.
-/
theorem transition_clause_has_step
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    {clause : NTMClause}
    (h :
      clause ∈ ntmTransitionsCNF M x t) :
    ∃ s, s < t ∧
      clause ∈ ntmTransitionStepCNF M x t s := by
  unfold ntmTransitionsCNF at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨s, hsRange, hsClause⟩
  exact ⟨s, List.mem_range.mp hsRange, hsClause⟩

/--
A clause in one transition step comes from one concrete control-state /
head-symbol transition case.
-/
theorem transition_step_clause_has_case
    {M : PolyNTMCandidate}
    {x : BitString}
    {t s : Nat}
    {clause : NTMClause}
    (h :
      clause ∈ ntmTransitionStepCNF M x t s) :
    ∃ q : Fin (M.stateCount + 1),
      ∃ a : Option Bool,
        clause ∈ ntmTransitionCaseCNF M x t s q a := by
  unfold ntmTransitionStepCNF at h
  rw [List.mem_flatten] at h
  rcases h with ⟨casesForQ, hCasesForQ, hClause⟩
  rw [List.mem_ofFn] at hCasesForQ
  rcases hCasesForQ with ⟨q, rfl⟩
  rw [List.mem_flatMap] at hClause
  rcases hClause with ⟨a, _ha, hClause⟩
  exact ⟨q, a, hClause⟩

inductive TransitionCaseKind where
  | haltedStutter
  | activeChoice
  deriving DecidableEq, Repr

inductive ActiveClauseKind where
  | guardChoice
  | choiceGuard
  | atMostOneChoice
  | choiceEffect
  deriving DecidableEq, Repr

/--
One clause occurrence refined to the concrete transition case and, when the
case is active, to the exact syntactic region inside ntmActiveChoiceCNF.
-/
structure TransitionInteractionSignature
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (core : ClauseUnsatCore M x t) where
  step : Nat
  step_lt : step < t
  q : Fin (M.stateCount + 1)
  a : Option Bool
  clause : NTMClause
  clause_in_core : clause ∈ core.clauses
  clause_in_case : clause ∈ ntmTransitionCaseCNF M x t step q a
  kind : TransitionCaseKind
  halted_proof :
    kind = .haltedStutter →
      clause ∈ ntmHaltedStutterCNF M x t step q a
  active_proof :
    kind = .activeChoice →
      clause ∈ ntmActiveChoiceCNF M x t step q a

/--
A clause in an active transition case belongs to exactly one of the four
syntactic regions used to build ntmActiveChoiceCNF.  The theorem returns a
disjunction because these regions can overlap extensionally as lists.
-/
theorem active_clause_region
    {M : PolyNTMCandidate}
    {x : BitString}
    {t s : Nat}
    {q : Fin (M.stateCount + 1)}
    {a : Option Bool}
    {clause : NTMClause}
    (h : clause ∈ ntmActiveChoiceCNF M x t s q a) :
    clause = ntmGuardChoiceClause M x t s q a ∨
    (∃ p ∈ ntmIndexedTransitions (M.machine.transition q a),
      clause ∈ ntmChoiceGuardCNF M x t s q a p.1) ∨
    clause ∈ ntmAtMostOneChoiceCNF M x t s q a ∨
    (∃ p ∈ ntmIndexedTransitions (M.machine.transition q a),
      clause ∈ ntmChoiceEffectCNF M x t s q a p) := by
  unfold ntmActiveChoiceCNF at h
  simp only [List.mem_append, List.mem_singleton] at h
  rcases h with hGuard | hRest
  · exact Or.inl hGuard
  · rcases hRest with hChoiceGuard | hRest
    · rw [List.mem_flatMap] at hChoiceGuard
      rcases hChoiceGuard with ⟨p, hp, hcl⟩
      exact Or.inr (Or.inl ⟨p, hp, hcl⟩)
    · rcases hRest with hAtMost | hEffect
      · exact Or.inr (Or.inr (Or.inl hAtMost))
      · rw [List.mem_flatMap] at hEffect
        rcases hEffect with ⟨p, hp, hcl⟩
        exact Or.inr (Or.inr (Or.inr ⟨p, hp, hcl⟩))

/--
Refine one concrete occurrence to halted-vs-active by the actual candidate
state flags.  No semantic endpoint is assumed.
-/
def signature_of_occurrence
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    {core : ClauseUnsatCore M x t}
    (occ : TransitionClauseOccurrence M x t core) :
    TransitionInteractionSignature M x t core := by
  rcases transition_step_clause_has_case occ.clause_in_step with
    ⟨q, a, hCase⟩
  by_cases hHalt :
      M.machine.accepting q || M.machine.rejecting q
  · exact
      { step := occ.step
        step_lt := occ.step_lt
        q := q
        a := a
        clause := occ.clause
        clause_in_core := occ.clause_in_core
        clause_in_case := hCase
        kind := .haltedStutter
        halted_proof := by
          intro _
          simpa [ntmTransitionCaseCNF, hHalt] using hCase
        active_proof := by
          intro h
          cases h }
  · exact
      { step := occ.step
        step_lt := occ.step_lt
        q := q
        a := a
        clause := occ.clause
        clause_in_core := occ.clause_in_core
        clause_in_case := hCase
        kind := .activeChoice
        halted_proof := by
          intro h
          cases h
        active_proof := by
          intro _
          simpa [ntmTransitionCaseCNF, hHalt] using hCase }

/--
Concrete active-effect payload.  This is the first signature that carries an
actual machine transition rather than only a syntactic case.
-/
structure ActiveEffectSignature
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (core : ClauseUnsatCore M x t) where
  base : TransitionInteractionSignature M x t core
  active : base.kind = .activeChoice
  entry :
    Nat × (Fin (M.stateCount + 1) × Option Bool × Direction)
  entry_mem :
    entry ∈ ntmIndexedTransitions
      (M.machine.transition base.q base.a)
  clause_in_effect :
    base.clause ∈
      ntmChoiceEffectCNF M x t base.step base.q base.a entry

/--
When an active signature's clause lies in the choice-effect region, extract
the concrete indexed machine transition.
-/
def active_effect_signature_of_region
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    {core : ClauseUnsatCore M x t}
    (sig : TransitionInteractionSignature M x t core)
    (hActive : sig.kind = .activeChoice)
    (hEffect :
      ∃ p ∈ ntmIndexedTransitions
          (M.machine.transition sig.q sig.a),
        sig.clause ∈
          ntmChoiceEffectCNF
            M x t sig.step sig.q sig.a p) :
    ActiveEffectSignature M x t core := by
  rcases hEffect with ⟨p, hp, hcl⟩
  exact
    { base := sig
      active := hActive
      entry := p
      entry_mem := hp
      clause_in_effect := hcl }

/--
The entry carried by an ActiveEffectSignature is a genuine transition of the
candidate, with a valid index and exact list value.
-/
theorem active_effect_entry_is_machine_transition
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    {core : ClauseUnsatCore M x t}
    (sig : ActiveEffectSignature M x t core) :
    ∃ hj :
        sig.entry.1 <
          (M.machine.transition sig.base.q sig.base.a).length,
      sig.entry.2 =
        (M.machine.transition sig.base.q sig.base.a).get
          ⟨sig.entry.1, hj⟩ := by
  have hj :=
    indexedTransitions_index_lt
      (M.machine.transition sig.base.q sig.base.a)
      sig.entry_mem
  refine ⟨hj, ?_⟩
  exact indexedTransitions_index_value
    (M.machine.transition sig.base.q sig.base.a)
    sig.entry.1 sig.entry.2 sig.entry_mem hj

/--
Every real Transit touch of an UNSAT core yields a concrete transition-step
occurrence.
-/
def occurrence_of_core_touch
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    {core : ClauseUnsatCore M x t}
    (hTouch :
      CoreTouches core (ntmTransitionsCNF M x t)) :
    TransitionClauseOccurrence M x t core := by
  rcases hTouch with ⟨clause, hCore, hTransit⟩
  rcases transition_clause_has_step hTransit with
    ⟨s, hs, hStep⟩
  exact
    { step := s
      step_lt := hs
      clause := clause
      clause_in_core := hCore
      clause_in_step := hStep }

/--
A genuine positive-time interaction conflict therefore exposes at least one
real transition step in every UNSAT core.
-/
def occurrence_of_interaction_core
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (ht : 0 < t)
    (C : OrbitalInteractionConflict M x t)
    (core : ClauseUnsatCore M x t) :
    TransitionClauseOccurrence M x t core :=
  occurrence_of_core_touch
    (interaction_conflict_core_requires_transition ht C core)

#print axioms MCore.Real.P03TransitionSignature.transition_clause_has_step
#print axioms MCore.Real.P03TransitionSignature.transition_step_clause_has_case
#print axioms MCore.Real.P03TransitionSignature.active_clause_region
#print axioms MCore.Real.P03TransitionSignature.active_effect_entry_is_machine_transition
/--
For the complemented deterministic candidate there is exactly one transition
entry for every state/head-symbol pair.
-/
@[simp] theorem complement_transition_singleton
    (candidate : PolyDTMCandidate)
    (q : Fin (candidate.stateCount + 1))
    (a : Option Bool) :
    (complementToNTMCandidate candidate).machine.transition q a =
      [candidate.machine.transition q a] := by
  rfl

@[simp] theorem complement_indexedTransitions_singleton
    (candidate : PolyDTMCandidate)
    (q : Fin (candidate.stateCount + 1))
    (a : Option Bool) :
    ntmIndexedTransitions
        ((complementToNTMCandidate candidate).machine.transition q a) =
      [(0, candidate.machine.transition q a)] := by
  rfl

/--
Hence two concrete indexed choices at the same complemented (q,a) cannot have
different indices.  This blocks the proposed "two distinct choices in one
interaction core" route.
-/
theorem complement_no_distinct_choice_indices
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
    j1 = j2 := by
  simp at h1 h2
  omega

#print axioms MCore.Real.P03TransitionSignature.complement_no_distinct_choice_indices
/--
For the complemented deterministic candidate, two indexed transition entries
at the same (q,a) are not merely equal in index: the complete indexed entries
are identical.
-/
theorem complement_indexed_entry_unique
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
    p1 = p2 := by
  simpa using h1.trans h2.symm

/--
Consequently, any two active-effect signatures at the same complemented
state/head-symbol pair carry the same concrete machine transition entry.
-/
theorem complement_active_effect_same_entry
    (candidate : PolyDTMCandidate)
    {x : BitString}
    {t : Nat}
    {core :
      ClauseUnsatCore
        (complementToNTMCandidate candidate) x t}
    (s1 s2 :
      ActiveEffectSignature
        (complementToNTMCandidate candidate) x t core)
    (hq : s1.base.q = s2.base.q)
    (ha : s1.base.a = s2.base.a) :
    s1.entry = s2.entry := by
  subst hq
  subst ha
  exact complement_indexed_entry_unique
    candidate s1.base.q s1.base.a
    s1.entry_mem s2.entry_mem

#print axioms MCore.Real.P03TransitionSignature.complement_indexed_entry_unique
#print axioms MCore.Real.P03TransitionSignature.complement_active_effect_same_entry
/--
An active-effect signature specialized to the deterministic complemented
candidate.  The transition payload is not arbitrary: it is exactly the
underlying deterministic TM transition at (q,a).
-/
structure DeterministicEffectSignature
    (candidate : PolyDTMCandidate)
    (x : BitString)
    (t : Nat)
    (core : ClauseUnsatCore (complementToNTMCandidate candidate) x t) where
  effect :
    ActiveEffectSignature
      (complementToNTMCandidate candidate) x t core
  index_zero : effect.entry.1 = 0
  transition_exact :
    effect.entry.2 =
      candidate.machine.transition effect.base.q effect.base.a

/-- Every complemented active-effect signature canonicalizes to index 0 and
the unique deterministic transition. -/
def deterministic_effect_signature
    (candidate : PolyDTMCandidate)
    {x : BitString}
    {t : Nat}
    {core : ClauseUnsatCore (complementToNTMCandidate candidate) x t}
    (effect :
      ActiveEffectSignature
        (complementToNTMCandidate candidate) x t core) :
    DeterministicEffectSignature candidate x t core := by
  have hEntry :
      effect.entry =
        (0, candidate.machine.transition effect.base.q effect.base.a) := by
    exact complement_indexed_entry_unique
      candidate effect.base.q effect.base.a
      effect.entry_mem
      (by simp)
  refine
    { effect := effect
      index_zero := ?_
      transition_exact := ?_ }
  · exact congrArg Prod.fst hEntry
  · exact congrArg Prod.snd hEntry

#print axioms MCore.Real.P03TransitionSignature.deterministic_effect_signature



#print axioms MCore.Real.P03TransitionSignature.signature_of_occurrence
#print axioms MCore.Real.P03TransitionSignature.occurrence_of_core_touch
#print axioms MCore.Real.P03TransitionSignature.occurrence_of_interaction_core

end P03TransitionSignature
end Real
end MCore
