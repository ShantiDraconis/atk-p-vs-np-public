import MCore.Real.P02BoundedComputationEncoding

namespace MCore
namespace Real
namespace P02BoundedComputationLogic

open CircuitK1
open CanonicalFinalProof
open P02BoundedComputationEncoding

theorem evalCNF_member_true
    (sigma : Assignment) (f : CNF) (c : Clause)
    (hc : c ∈ f)
    (htrue : evalCNF sigma f = true) :
    evalClause sigma c = true := by
  induction f with
  | nil =>
      cases hc
  | cons d ds ih =>
      have hparts :
          evalClause sigma d = true ∧ evalCNF sigma ds = true := by
        exact (bool_and_eq_true_iff _ _).mp htrue
      cases hc with
      | head =>
          exact hparts.1
      | tail _ hc' =>
          exact ih hc' hparts.2

theorem evalCNF_true_of_forall_mem
    (sigma : Assignment) (f : CNF)
    (h : ∀ c ∈ f, evalClause sigma c = true) :
    evalCNF sigma f = true := by
  induction f with
  | nil =>
      rfl
  | cons c cs ih =>
      apply (bool_and_eq_true_iff _ _).mpr
      constructor
      · exact h c (List.Mem.head cs)
      · apply ih
        intro d hd
        exact h d (List.Mem.tail c hd)

theorem evalCNF_subset_true
    (sigma : Assignment) (small big : CNF)
    (hbig : evalCNF sigma big = true)
    (hsub : ∀ c ∈ small, c ∈ big) :
    evalCNF sigma small = true := by
  apply evalCNF_true_of_forall_mem
  intro c hc
  exact evalCNF_member_true sigma big c (hsub c hc) hbig

theorem evalClause_append
    (sigma : Assignment) (a b : Clause) :
    evalClause sigma (a ++ b) =
      Bool.or (evalClause sigma a) (evalClause sigma b) := by
  induction a with
  | nil =>
      simp [evalClause]
  | cons l ls ih =>
      simp [evalClause, ih, Bool.or_assoc]

theorem evalClause_append_single_of_false
    (sigma : Assignment) (guard : Clause) (l : Literal)
    (hguard : evalClause sigma guard = false) :
    evalClause sigma (guard ++ [l]) = evalLiteral sigma l := by
  rw [evalClause_append, hguard]
  simp [evalClause]

theorem eval_litFor_true_iff
    (sigma : Assignment) (v : Nat) (value : Bool) :
    evalLiteral sigma (litFor v value) = true ↔
      sigma v = value := by
  cases value <;> cases h : sigma v <;>
    simp [litFor, pos, neg, evalLiteral, h]

theorem setStateClauses_forces
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (t s : Nat)
    (target q : Fin (M.stateCount + 1))
    (hguard : evalClause sigma guard = false)
    (hcnf : evalCNF sigma (setStateClauses guard M t s target) = true) :
    sigma (stateVar M t s q) = decide (q = target) := by
  have hmem :
      guard ++ [litFor (stateVar M t s q) (decide (q = target))] ∈
        setStateClauses guard M t s target := by
    unfold setStateClauses
    exact (List.mem_ofFn).2 ⟨q, rfl⟩
  have hclause :=
    evalCNF_member_true sigma
      (setStateClauses guard M t s target)
      (guard ++ [litFor (stateVar M t s q) (decide (q = target))])
      hmem hcnf
  have hlit :
      evalLiteral sigma
        (litFor (stateVar M t s q) (decide (q = target))) = true := by
    simpa [evalClause_append_single_of_false sigma guard
      (litFor (stateVar M t s q) (decide (q = target))) hguard]
      using hclause
  exact
    (eval_litFor_true_iff sigma
      (stateVar M t s q) (decide (q = target))).mp hlit

theorem setSymbolClauses_forces
    (sigma : Assignment)
    (guard : Clause)
    (varAt : Option Bool → Nat)
    (target a : Option Bool)
    (hguard : evalClause sigma guard = false)
    (hcnf : evalCNF sigma (setSymbolClauses guard varAt target) = true) :
    sigma (varAt a) = decide (a = target) := by
  have hmem :
      guard ++ [litFor (varAt a) (decide (a = target))] ∈
        setSymbolClauses guard varAt target := by
    cases a with
    | none =>
        simp [setSymbolClauses, alphabet]
    | some b =>
        cases b <;> simp [setSymbolClauses, alphabet]
  have hclause :=
    evalCNF_member_true sigma
      (setSymbolClauses guard varAt target)
      (guard ++ [litFor (varAt a) (decide (a = target))])
      hmem hcnf
  have hlit :
      evalLiteral sigma
        (litFor (varAt a) (decide (a = target))) = true := by
    simpa [evalClause_append_single_of_false sigma guard
      (litFor (varAt a) (decide (a = target))) hguard]
      using hclause
  exact
    (eval_litFor_true_iff sigma
      (varAt a) (decide (a = target))).mp hlit

theorem copySymbolClauses_forces
    (sigma : Assignment)
    (guard : Clause)
    (oldVar newVar : Option Bool → Nat)
    (a : Option Bool)
    (hguard : evalClause sigma guard = false)
    (hcnf : evalCNF sigma (copySymbolClauses guard oldVar newVar) = true) :
    sigma (newVar a) = sigma (oldVar a) := by
  have hmem1 :
      guard ++ [neg (oldVar a), pos (newVar a)] ∈
        copySymbolClauses guard oldVar newVar := by
    cases a with
    | none =>
        simp [copySymbolClauses, alphabet]
    | some b =>
        cases b <;> simp [copySymbolClauses, alphabet]
  have hmem2 :
      guard ++ [pos (oldVar a), neg (newVar a)] ∈
        copySymbolClauses guard oldVar newVar := by
    cases a with
    | none =>
        simp [copySymbolClauses, alphabet]
    | some b =>
        cases b <;> simp [copySymbolClauses, alphabet]
  have h1 := evalCNF_member_true sigma
    (copySymbolClauses guard oldVar newVar)
    (guard ++ [neg (oldVar a), pos (newVar a)]) hmem1 hcnf
  have h2 := evalCNF_member_true sigma
    (copySymbolClauses guard oldVar newVar)
    (guard ++ [pos (oldVar a), neg (newVar a)]) hmem2 hcnf
  rw [evalClause_append, hguard] at h1 h2
  simp [evalClause, evalLiteral, neg, pos] at h1 h2
  cases hold : sigma (oldVar a) <;>
    cases hnew : sigma (newVar a) <;>
    simp_all

#print axioms MCore.Real.P02BoundedComputationLogic.evalCNF_member_true
#print axioms MCore.Real.P02BoundedComputationLogic.evalClause_append
#print axioms MCore.Real.P02BoundedComputationLogic.eval_litFor_true_iff
#print axioms MCore.Real.P02BoundedComputationLogic.setStateClauses_forces
#print axioms MCore.Real.P02BoundedComputationLogic.setSymbolClauses_forces
#print axioms MCore.Real.P02BoundedComputationLogic.copySymbolClauses_forces

end P02BoundedComputationLogic
end Real
end MCore
