import MCore.Real.P03Lemmas

namespace MCore
namespace Real
namespace P03InteractionConflict

open CanonicalFinalProof
open PNPNTMTableauEncoding
open P03MaterialLaw
open P03Lemmas

/-- Variables occurring in one NTM clause. -/
def ClauseVarSet (clause : NTMClause) : Finset Nat :=
  (clause.map NTMLiteral.var).toFinset

/-- Variables occurring anywhere in an NTM CNF. -/
def CNFVarSet (F : NTMCNF) : Finset Nat :=
  (F.flatMap (fun clause => clause.map NTMLiteral.var)).toFinset

theorem var_mem_CNFVarSet_of_mem
    {F : NTMCNF}
    {clause : NTMClause}
    {lit : NTMLiteral}
    (hcl : clause ∈ F)
    (hl : lit ∈ clause) :
    lit.var ∈ CNFVarSet F := by
  simp [CNFVarSet]
  exact ⟨clause, hcl, lit, hl, rfl⟩

theorem evalNTMLiteral_eq_of_agree
    {sigma1 sigma2 : Assignment}
    {lit : NTMLiteral}
    (h : sigma1 lit.var = sigma2 lit.var) :
    evalNTMLiteral sigma1 lit = evalNTMLiteral sigma2 lit := by
  simp [evalNTMLiteral, h]

theorem evalNTMClause_eq_of_agree_on_varset
    {clause : NTMClause}
    {sigma1 sigma2 : Assignment}
    (h :
      ∀ v ∈ ClauseVarSet clause,
        sigma1 v = sigma2 v) :
    evalNTMClause sigma1 clause = evalNTMClause sigma2 clause := by
  induction clause with
  | nil =>
      rfl
  | cons lit rest ih =>
      have hlit : sigma1 lit.var = sigma2 lit.var := by
        apply h
        simp [ClauseVarSet]
      have hrest :
          ∀ v ∈ ClauseVarSet rest,
            sigma1 v = sigma2 v := by
        intro v hv
        apply h
        simpa [ClauseVarSet] using hv
      simp only [evalNTMClause]
      rw [evalNTMLiteral_eq_of_agree hlit, ih hrest]

theorem evalNTMCNF_eq_of_agree_on_varset
    {F : NTMCNF}
    {sigma1 sigma2 : Assignment}
    (h :
      ∀ v ∈ CNFVarSet F,
        sigma1 v = sigma2 v) :
    evalNTMCNF sigma1 F = evalNTMCNF sigma2 F := by
  induction F with
  | nil =>
      rfl
  | cons clause rest ih =>
      have hclause :
          ∀ v ∈ ClauseVarSet clause,
            sigma1 v = sigma2 v := by
        intro v hv
        apply h
        simp [CNFVarSet, ClauseVarSet] at hv ⊢
        exact Or.inl hv
      have hrest :
          ∀ v ∈ CNFVarSet rest,
            sigma1 v = sigma2 v := by
        intro v hv
        apply h
        simpa [CNFVarSet] using hv
      simp only [evalNTMCNF]
      rw [evalNTMClause_eq_of_agree_on_varset hclause, ih hrest]

theorem mem_CNFVarSet_iff
    {F : NTMCNF}
    {v : Nat} :
    v ∈ CNFVarSet F ↔
      ∃ clause ∈ F, ∃ lit ∈ clause, lit.var = v := by
  simp [CNFVarSet]

theorem terminal_var_classifier
    {M : PolyNTMCandidate}
    {t v : Nat}
    (hv : v ∈ CNFVarSet (ntmFinalAcceptanceCNF M t)) :
    ∃ q : Fin (M.stateCount + 1),
      M.machine.accepting q = true ∧
      v = ntmStateVar M t t q := by
  rcases (mem_CNFVarSet_iff.mp hv) with
    ⟨clause, hclause, lit, hlit, hvar⟩
  have hclauseEq : clause = ntmAcceptingStateLits M t := by
    simpa [ntmFinalAcceptanceCNF] using hclause
  subst clause
  unfold ntmAcceptingStateLits at hlit
  rcases filterMap_mem_exists
      (fun q : Fin (M.stateCount + 1) =>
        if M.machine.accepting q = true then
          some (ntmPos (ntmStateVar M t t q))
        else none)
      (List.ofFn fun q : Fin (M.stateCount + 1) => q)
      lit hlit with
    ⟨q, _hqmem, hq⟩
  by_cases hacc : M.machine.accepting q = true
  · simp [hacc] at hq
    subst lit
    refine ⟨q, hacc, ?_⟩
    simpa [ntmPos] using hvar.symm
  · simp [hacc] at hq

/--
Every variable in the initial block belongs to exactly one of the four
time-zero regions: state, head, left tape, or right tape.
-/
theorem initial_var_classifier
    {M : PolyNTMCandidate}
    {x : BitString}
    {t v : Nat}
    (hv : v ∈ CNFVarSet (ntmInitialCNF M x t)) :
    (∃ q : Fin (M.stateCount + 1),
        v = ntmStateVar M t 0 q) ∨
    (∃ a : Option Bool,
        v = ntmHeadVar M t 0 a) ∨
    (∃ i : Nat, i < ntmRadius x t ∧
      ∃ a : Option Bool,
        v = ntmLeftVar M x t 0 i a) ∨
    (∃ i : Nat, i < ntmRadius x t ∧
      ∃ a : Option Bool,
        v = ntmRightVar M x t 0 i a) := by
  rcases (mem_CNFVarSet_iff.mp hv) with
    ⟨clause, hclause, lit, hlit, hvar⟩
  unfold ntmInitialCNF at hclause
  simp only [List.mem_append] at hclause
  rcases hclause with hState | hclause
  · unfold ntmSetStateClauses at hState
    rw [List.mem_ofFn] at hState
    rcases hState with ⟨q, rfl⟩
    simp at hlit
    subst lit
    left
    refine ⟨q, ?_⟩
    simpa [ntmLitFor_var] using hvar.symm
  · rcases hclause with hHead | hclause
    · unfold ntmSetSymbolClauses at hHead
      rw [List.mem_map] at hHead
      rcases hHead with ⟨a, _ha, rfl⟩
      simp at hlit
      subst lit
      right
      left
      refine ⟨a, ?_⟩
      simpa [ntmLitFor_var] using hvar.symm
    · rcases hclause with hLeft | hRight
      · rw [List.mem_flatMap] at hLeft
        rcases hLeft with ⟨i, hi, hset⟩
        have hir : i < ntmRadius x t := List.mem_range.mp hi
        unfold ntmSetLeftCell ntmSetSymbolClauses at hset
        rw [List.mem_map] at hset
        rcases hset with ⟨a, _ha, rfl⟩
        simp at hlit
        subst lit
        right
        right
        left
        refine ⟨i, hir, a, ?_⟩
        simpa [ntmLitFor_var] using hvar.symm
      · rw [List.mem_flatMap] at hRight
        rcases hRight with ⟨i, hi, hset⟩
        have hir : i < ntmRadius x t := List.mem_range.mp hi
        unfold ntmSetRightCell ntmSetSymbolClauses at hset
        rw [List.mem_map] at hset
        rcases hset with ⟨a, _ha, rfl⟩
        simp at hlit
        subst lit
        right
        right
        right
        refine ⟨i, hir, a, ?_⟩
        simpa [ntmLitFor_var] using hvar.symm

/--
A genuine UNSAT core: actual clauses, together with membership in the full
tableau and an UNSAT certificate.  This is stronger than a block-support mask.
-/
structure ClauseUnsatCore
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) where
  clauses : NTMCNF
  subset_whole :
    ∀ clause ∈ clauses,
      clause ∈ boundedExecTableauCNF_NTM M x t
  unsat : CNFUnsat clauses

/-- A core touches a concrete CNF block when it contains a clause from it. -/
def CoreTouches
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (core : ClauseUnsatCore M x t)
    (block : NTMCNF) : Prop :=
  ∃ clause, clause ∈ core.clauses ∧ clause ∈ block

/-- The full tableau itself is always a legitimate core when it is UNSAT. -/
def fullUnsatCore
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (h : CNFUnsat (boundedExecTableauCNF_NTM M x t)) :
    ClauseUnsatCore M x t where
  clauses := boundedExecTableauCNF_NTM M x t
  subset_whole := by
    intro clause hclause
    exact hclause
  unsat := h

/--
A non-degenerate interaction conflict.

The prefix Init+Transit is satisfiable, Terminal is satisfiable in isolation,
but the complete tableau is unsatisfiable.  Thus the contradiction cannot be
explained by a terminal-empty-clause degeneracy or by an inconsistent physical
prefix alone.
-/
structure OrbitalInteractionConflict
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) where
  h_term_sat :
    CNFSat (ntmFinalAcceptanceCNF M t)
  h_prefix_sat :
    CNFSat (supportedCNF initTransitSupport M x t)
  h_whole_unsat :
    CNFUnsat (boundedExecTableauCNF_NTM M x t)

/-- A satisfiable prefix has a satisfiable Init projection. -/
theorem init_sat_of_prefix_sat
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (h :
      CNFSat (supportedCNF initTransitSupport M x t)) :
    CNFSat (ntmInitialCNF M x t) := by
  rcases h with ⟨sigma, hSat⟩
  refine ⟨sigma, ?_⟩
  rw [supportedCNF_initTransitSupport] at hSat
  exact
    (evalNTMCNF_append sigma
      (ntmInitialCNF M x t)
      (ntmTransitionsCNF M x t)).1 hSat |>.1

/-- If a larger CNF is SAT, every sub-CNF selected by clause membership is SAT. -/
theorem cnf_sat_of_clause_subset
    {small big : NTMCNF}
    {sigma : Assignment}
    (hBig : evalNTMCNF sigma big = true)
    (hSub : ∀ clause ∈ small, clause ∈ big) :
    evalNTMCNF sigma small = true := by
  induction small with
  | nil =>
      rfl
  | cons clause rest ih =>
      have hClause :
          evalNTMClause sigma clause = true := by
        exact evalNTMCNF_of_mem sigma big clause hBig
          (hSub clause (by simp))
      have hRest :
          evalNTMCNF sigma rest = true := by
        apply ih
        intro c hc
        exact hSub c (by simp [hc])
      simp [evalNTMCNF, hClause, hRest]

/-- UNSAT is monotone upward under clause inclusion. -/
theorem cnf_unsat_of_unsat_subset
    {small big : NTMCNF}
    (hSmall : CNFUnsat small)
    (hSub : ∀ clause ∈ small, clause ∈ big) :
    CNFUnsat big := by
  intro sigma
  by_cases hBig : evalNTMCNF sigma big = true
  · have hSmallSat := cnf_sat_of_clause_subset hBig hSub
    have hSmallFalse := hSmall sigma
    rw [hSmallSat] at hSmallFalse
    contradiction
  · cases hEval : evalNTMCNF sigma big
    · rfl
    · exact False.elim (hBig hEval)

/-- Degenerate case: Terminal is already contradictory without Init/Transit. -/
def IsTerminalDegenerate
    (M : PolyNTMCandidate)
    (t : Nat) : Prop :=
  CNFUnsat (ntmFinalAcceptanceCNF M t)

/-- Genuine interaction case used by the P03 material route. -/
def IsInteractionConflict
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Prop :=
  Nonempty (OrbitalInteractionConflict M x t)

/-- Every interaction conflict canonically yields the full conflict witness. -/
def OrbitalInteractionConflict.toClauseConflictWitness
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (C : OrbitalInteractionConflict M x t) :
    ClauseConflictWitness M x t :=
  (fullConflictExtractor M).locate x t C.h_whole_unsat

/--
If Terminal is satisfiable, its accepting-state clause cannot be empty.
This separates genuine interaction conflicts from the [[]] terminal
degeneracy.
-/
theorem terminal_sat_implies_nonempty_lits
    {M : PolyNTMCandidate}
    {t : Nat}
    (h : CNFSat (ntmFinalAcceptanceCNF M t)) :
    ntmAcceptingStateLits M t ≠ [] := by
  intro hEmpty
  rcases h with ⟨sigma, hSat⟩
  simp [ntmFinalAcceptanceCNF, hEmpty, evalNTMCNF, evalNTMClause] at hSat

/--
For positive time, a terminal state variable cannot be the initial state
variable.  This is the only Init/Terminal separation fact that needs t > 0.
-/
theorem terminal_state_ne_initial_state
    (M : PolyNTMCandidate)
    (t : Nat)
    (ht : 0 < t)
    (q0 qt : Fin (M.stateCount + 1)) :
    ntmStateVar M t 0 q0 ≠ ntmStateVar M t t qt := by
  intro hEq
  have h := ntmStateVar_injective M t 0 t q0 qt hEq
  omega

/-- Terminal state variables lie strictly below the head-variable region. -/
theorem terminal_state_ne_initial_head
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (qt : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ntmStateVar M t t qt ≠ ntmHeadVar M t 0 a := by
  exact stateVar_ne_headVar M x t t 0 qt a (by omega) (by omega)

/-- Terminal state variables cannot collide with initial left-tape variables. -/
theorem terminal_state_ne_initial_left
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t)
    (qt : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ntmStateVar M t t qt ≠ ntmLeftVar M x t 0 i a := by
  have hs := ntmStateVar_lt_headBase M t t qt (by omega)
  have hl := (ntmLeftVar_range M x t 0 i a (by omega) hi).1
  have hb : ntmHeadBase M t ≤ ntmLeftBase M x t := by
    simp [ntmLeftBase]
  omega

/-- Terminal state variables cannot collide with initial right-tape variables. -/
theorem terminal_state_ne_initial_right
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t)
    (qt : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ntmStateVar M t t qt ≠ ntmRightVar M x t 0 i a := by
  have hs := ntmStateVar_lt_headBase M t t qt (by omega)
  have hr := (ntmRightVar_range M x t 0 i a (by omega) hi).1
  have hb : ntmHeadBase M t ≤ ntmRightBase M x t := by
    simp [ntmRightBase, ntmLeftBase]
  omega

#print axioms MCore.Real.P03InteractionConflict.mem_CNFVarSet_iff
#print axioms MCore.Real.P03InteractionConflict.terminal_var_classifier
#print axioms MCore.Real.P03InteractionConflict.initial_var_classifier
#print axioms MCore.Real.P03InteractionConflict.var_mem_CNFVarSet_of_mem
#print axioms MCore.Real.P03InteractionConflict.evalNTMClause_eq_of_agree_on_varset
#print axioms MCore.Real.P03InteractionConflict.evalNTMCNF_eq_of_agree_on_varset
/--
For positive clock, Init and Terminal use disjoint variable sets.
Terminal contains only state variables at time t; Init contains the four
time-zero regions classified above.
-/
theorem init_terminal_vars_disjoint
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (ht : 0 < t) :
    Disjoint
      (CNFVarSet (ntmInitialCNF M x t))
      (CNFVarSet (ntmFinalAcceptanceCNF M t)) := by
  rw [Finset.disjoint_left]
  intro v hvI hvT
  rcases terminal_var_classifier hvT with ⟨qt, _hacc, hvTerminal⟩
  rcases initial_var_classifier hvI with
    hState | hHead | hLeft | hRight
  · rcases hState with ⟨q0, hvInitial⟩
    have hEq :
        ntmStateVar M t 0 q0 =
          ntmStateVar M t t qt := by
      calc
        ntmStateVar M t 0 q0 = v := hvInitial.symm
        _ = ntmStateVar M t t qt := hvTerminal
    exact (terminal_state_ne_initial_state M t ht q0 qt) hEq
  · rcases hHead with ⟨a, hvInitial⟩
    have hEq :
        ntmStateVar M t t qt =
          ntmHeadVar M t 0 a := by
      calc
        ntmStateVar M t t qt = v := hvTerminal.symm
        _ = ntmHeadVar M t 0 a := hvInitial
    exact (terminal_state_ne_initial_head M x t qt a) hEq
  · rcases hLeft with ⟨i, hi, a, hvInitial⟩
    have hEq :
        ntmStateVar M t t qt =
          ntmLeftVar M x t 0 i a := by
      calc
        ntmStateVar M t t qt = v := hvTerminal.symm
        _ = ntmLeftVar M x t 0 i a := hvInitial
    exact (terminal_state_ne_initial_left M x t i hi qt a) hEq
  · rcases hRight with ⟨i, hi, a, hvInitial⟩
    have hEq :
        ntmStateVar M t t qt =
          ntmRightVar M x t 0 i a := by
      calc
        ntmStateVar M t t qt = v := hvTerminal.symm
        _ = ntmRightVar M x t 0 i a := hvInitial
    exact (terminal_state_ne_initial_right M x t i hi qt a) hEq

#print axioms MCore.Real.P03InteractionConflict.init_terminal_vars_disjoint
/--
Disjoint satisfiable CNFs can be satisfied by one combined assignment.
This is specialized to Init and Terminal because that is the material bridge
needed by the interaction-conflict route.
-/
theorem init_terminal_sat_of_both
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (ht : 0 < t)
    (hI : CNFSat (ntmInitialCNF M x t))
    (hT : CNFSat (ntmFinalAcceptanceCNF M t)) :
    CNFSat
      (ntmInitialCNF M x t ++
        ntmFinalAcceptanceCNF M t) := by
  rcases hI with ⟨sigmaI, hsigmaI⟩
  rcases hT with ⟨sigmaT, hsigmaT⟩
  have hDisj :=
    init_terminal_vars_disjoint M x t ht
  let sigma : Assignment := fun v =>
    if v ∈ CNFVarSet (ntmInitialCNF M x t) then
      sigmaI v
    else
      sigmaT v
  have hAgreeI :
      ∀ v ∈ CNFVarSet (ntmInitialCNF M x t),
        sigma v = sigmaI v := by
    intro v hv
    simp [sigma, hv]
  have hAgreeT :
      ∀ v ∈ CNFVarSet (ntmFinalAcceptanceCNF M t),
        sigma v = sigmaT v := by
    intro v hvT
    have hvI :
        v ∉ CNFVarSet (ntmInitialCNF M x t) := by
      intro hvI
      exact (Finset.disjoint_left.mp hDisj) hvI hvT
    simp [sigma, hvI]
  have hSatI :
      evalNTMCNF sigma (ntmInitialCNF M x t) = true := by
    rw [evalNTMCNF_eq_of_agree_on_varset hAgreeI]
    exact hsigmaI
  have hSatT :
      evalNTMCNF sigma (ntmFinalAcceptanceCNF M t) = true := by
    rw [evalNTMCNF_eq_of_agree_on_varset hAgreeT]
    exact hsigmaT
  refine ⟨sigma, ?_⟩
  exact
    (evalNTMCNF_append sigma
      (ntmInitialCNF M x t)
      (ntmFinalAcceptanceCNF M t)).2
      ⟨hSatI, hSatT⟩

#print axioms MCore.Real.P03InteractionConflict.init_terminal_sat_of_both
#print axioms MCore.Real.P03InteractionConflict.init_sat_of_prefix_sat
#print axioms MCore.Real.P03InteractionConflict.cnf_sat_of_clause_subset
#print axioms MCore.Real.P03InteractionConflict.cnf_unsat_of_unsat_subset
/--
In a genuine positive-time interaction conflict, every actual UNSAT core of
the full tableau must contain at least one transition clause.

This is the nontrivial Transit-necessity statement: it is not a consequence of
fullSupport by definition.
-/
theorem interaction_conflict_core_requires_transition
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (ht : 0 < t)
    (C : OrbitalInteractionConflict M x t)
    (core : ClauseUnsatCore M x t) :
    CoreTouches core (ntmTransitionsCNF M x t) := by
  by_contra hNoTransit
  have hSubsetInitTerminal :
      ∀ clause ∈ core.clauses,
        clause ∈
          ntmInitialCNF M x t ++
            ntmFinalAcceptanceCNF M t := by
    intro clause hCore
    have hWhole := core.subset_whole clause hCore
    unfold boundedExecTableauCNF_NTM at hWhole
    simp only [List.mem_append] at hWhole
    rcases hWhole with hInit | hRest
    · exact List.mem_append_left _ hInit
    · rcases hRest with hTransit | hTerminal
      · exfalso
        apply hNoTransit
        exact ⟨clause, hCore, hTransit⟩
      · exact List.mem_append_right _ hTerminal
  have hInitTerminalUnsat :
      CNFUnsat
        (ntmInitialCNF M x t ++
          ntmFinalAcceptanceCNF M t) :=
    cnf_unsat_of_unsat_subset core.unsat hSubsetInitTerminal
  have hInit :
      CNFSat (ntmInitialCNF M x t) :=
    init_sat_of_prefix_sat C.h_prefix_sat
  have hInitTerminalSat :
      CNFSat
        (ntmInitialCNF M x t ++
          ntmFinalAcceptanceCNF M t) :=
    init_terminal_sat_of_both M x t ht hInit C.h_term_sat
  rcases hInitTerminalSat with ⟨sigma, hSat⟩
  have hFalse := hInitTerminalUnsat sigma
  rw [hSat] at hFalse
  contradiction

#print axioms MCore.Real.P03InteractionConflict.interaction_conflict_core_requires_transition


#print axioms MCore.Real.P03InteractionConflict.terminal_sat_implies_nonempty_lits
#print axioms MCore.Real.P03InteractionConflict.terminal_state_ne_initial_state
#print axioms MCore.Real.P03InteractionConflict.terminal_state_ne_initial_head
#print axioms MCore.Real.P03InteractionConflict.terminal_state_ne_initial_left
#print axioms MCore.Real.P03InteractionConflict.terminal_state_ne_initial_right

end P03InteractionConflict
end Real
end MCore
