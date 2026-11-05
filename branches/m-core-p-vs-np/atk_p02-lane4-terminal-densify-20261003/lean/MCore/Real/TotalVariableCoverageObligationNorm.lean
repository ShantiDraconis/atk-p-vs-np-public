import MCore.Real.Claim4NormalizedProgress
import MCore.Real.Claim7VariableCoverage

namespace MCore
namespace Real
namespace P02Lane4TotalVariableCoverageNorm

open CircuitK1
open P02BoundedComputationEncoding
open Claim4NormalizedProgress
open Claim7VariableCoverage

private theorem mem_zipIdx_of_mem
    {α : Type} (x : α) :
    ∀ (l : List α) (n : Nat), x ∈ l → ∃ i : Nat, (x, i) ∈ l.zipIdx n := by
  intro l
  induction l with
  | nil =>
      intro n hx
      simp at hx
  | cons a as ih =>
      intro n hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨n, by simp⟩
      · obtain ⟨i, hi⟩ := ih (n + 1) hx
        exact ⟨i, by simp [hi]⟩

/-- Every payload variable is copied into the total-variable coverage core. -/
theorem payload_var_mem_coverageCore
    {payload : CNF} {v : Nat}
    (hv : v ∈ cnfVarList payload) :
    v ∈ cnfVarList (coverageCore payload) := by
  obtain ⟨i, hi⟩ :=
    mem_zipIdx_of_mem v (cnfVarList payload) 0 hv
  have hclause :
      [pos v, pos (cnfVarBound payload + 2 * i)] ∈ coverageCore payload := by
    simp only [coverageCore, List.mem_flatMap]
    refine ⟨(v, i), hi, ?_⟩
    simp [coverageClauses]
  apply Claim7VariableCoverage.mem_eraseDups_iff.mpr
  simp only [List.mem_flatMap]
  refine ⟨[pos v, pos (cnfVarBound payload + 2 * i)], hclause, ?_⟩
  simp [pos]

#print axioms MCore.Real.P02Lane4TotalVariableCoverageNorm.payload_var_mem_coverageCore

/-- Restricting a literal whose variable is free leaves its normalized circuit unchanged. -/
private theorem restrict_literalCircuit_of_none
    (ρ : Restriction) (l : Literal)
    (hρ : ρ l.var = none) :
    MCore.CircuitK1.restrict ρ (literalCircuit l) = literalCircuit l := by
  cases l with
  | mk v p =>
      cases p <;> simp [literalCircuit, MCore.CircuitK1.restrict, hρ]

private theorem restrict_smartOr_of_fixed
    (ρ : Restriction) (x y : Circuit)
    (hx : MCore.CircuitK1.restrict ρ x = x)
    (hy : MCore.CircuitK1.restrict ρ y = y) :
    MCore.CircuitK1.restrict ρ (smartOr x y) = smartOr x y := by
  cases x <;> cases y <;>
    simp_all [smartOr, MCore.CircuitK1.restrict] <;>
    split <;> simp_all [MCore.CircuitK1.restrict]

private theorem restrict_smartAnd_of_fixed
    (ρ : Restriction) (x y : Circuit)
    (hx : MCore.CircuitK1.restrict ρ x = x)
    (hy : MCore.CircuitK1.restrict ρ y = y) :
    MCore.CircuitK1.restrict ρ (smartAnd x y) = smartAnd x y := by
  cases x <;> cases y <;>
    simp_all [smartAnd, MCore.CircuitK1.restrict] <;>
    split <;> simp_all [MCore.CircuitK1.restrict]

/-- A restriction free on every variable of a clause fixes its normalized circuit. -/
private theorem restrict_clauseCircuitNorm_id
    (ρ : Restriction) (c : Clause)
    (hfree : ∀ l : Literal, l ∈ c → ρ l.var = none) :
    MCore.CircuitK1.restrict ρ (clauseCircuitNorm c) = clauseCircuitNorm c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
      cases ls with
      | nil =>
          have hl : ρ l.var = none := hfree l (by simp)
          simpa [clauseCircuitNorm] using restrict_literalCircuit_of_none ρ l hl
      | cons l2 ls2 =>
          have hl : ρ l.var = none := hfree l (by simp)
          have htail : ∀ x : Literal, x ∈ (l2 :: ls2) → ρ x.var = none := by
            intro x hx
            exact hfree x (by simp [hx])
          exact restrict_smartOr_of_fixed ρ
            (literalCircuit l) (clauseCircuitNorm (l2 :: ls2))
            (restrict_literalCircuit_of_none ρ l hl)
            (ih htail)

/-- A restriction free on every CNF variable fixes the normalized CNF circuit. -/
private theorem restrict_cnfCircuitNorm_id
    (ρ : Restriction) (f : CNF)
    (hfree : ∀ v : Nat, v ∈ cnfVarList f → ρ v = none) :
    MCore.CircuitK1.restrict ρ (cnfCircuitNorm f) = cnfCircuitNorm f := by
  induction f with
  | nil => rfl
  | cons c cs ih =>
      have hcfree : ∀ l : Literal, l ∈ c → ρ l.var = none := by
        intro l hl
        exact hfree l.var
          (literal_var_mem_cnfVarList (f := c :: cs) (c := c) (l := l) (by simp) hl)
      cases cs with
      | nil =>
          simpa [cnfCircuitNorm] using restrict_clauseCircuitNorm_id ρ c hcfree
      | cons c2 cs2 =>
          have htail : ∀ v : Nat, v ∈ cnfVarList (c2 :: cs2) → ρ v = none := by
            intro v hv
            exact hfree v
              (cnfVarList_right_subset_append [c] (c2 :: cs2) v hv)
          exact restrict_smartAnd_of_fixed ρ
            (clauseCircuitNorm c) (cnfCircuitNorm (c2 :: cs2))
            (restrict_clauseCircuitNorm_id ρ c hcfree)
            (ih htail)

/-- TARGET2a: if the restriction fixes none of the CNF variables, normalized progress is impossible. -/
theorem no_restricted_var_implies_no_progress_norm
    (ρ : Restriction) (f : CNF)
    (hfree : ∀ v : Nat, v ∈ cnfVarList f → ρ v = none) :
    ¬ RestrictionProgressNorm ρ (cnfCircuitNorm f) := by
  intro hprogress
  apply hprogress
  simp [DNorm, simplify_cnfCircuitNorm_idem,
    restrict_cnfCircuitNorm_id ρ f hfree]

#print axioms MCore.Real.P02Lane4TotalVariableCoverageNorm.no_restricted_var_implies_no_progress_norm


/-- TARGET2b: normalized progress exposes at least one restricted CNF variable. -/
theorem progressNorm_implies_restricted_var
    (ρ : Restriction) (f : CNF)
    (hprogress : RestrictionProgressNorm ρ (cnfCircuitNorm f)) :
    ∃ v : Nat, v ∈ cnfVarList f ∧ ρ v ≠ none := by
  apply Classical.byContradiction
  intro hex
  have hfree : ∀ v : Nat, v ∈ cnfVarList f → ρ v = none := by
    intro v hv
    cases hρ : ρ v with
    | none => rfl
    | some b =>
        exfalso
        apply hex
        exact ⟨v, hv, by simp [hρ]⟩
  exact (no_restricted_var_implies_no_progress_norm ρ f hfree) hprogress

#print axioms MCore.Real.P02Lane4TotalVariableCoverageNorm.progressNorm_implies_restricted_var

/-- Syntactic occurrence of an input variable in a circuit. -/
private def OccursInput (v : Nat) : Circuit → Prop
  | .input i => i = v
  | .const _ => False
  | .not c => OccursInput v c
  | .and a b => OccursInput v a ∨ OccursInput v b
  | .or a b => OccursInput v a ∨ OccursInput v b

private def NonConstCircuit : Circuit → Prop
  | .const _ => False
  | _ => True

private theorem literalCircuit_nonconst (l : Literal) :
    NonConstCircuit (literalCircuit l) := by
  cases l with
  | mk v p =>
      cases p <;> simp [literalCircuit, NonConstCircuit]

private theorem occurs_literalCircuit_self (l : Literal) :
    OccursInput l.var (literalCircuit l) := by
  cases l with
  | mk v p =>
      cases p <;> simp [literalCircuit, OccursInput]

private theorem smartOr_nonconst
    (x y : Circuit)
    (hx : NonConstCircuit x) (hy : NonConstCircuit y) :
    NonConstCircuit (smartOr x y) := by
  cases x <;> cases y <;>
    simp_all [NonConstCircuit, smartOr]

private theorem smartAnd_nonconst
    (x y : Circuit)
    (hx : NonConstCircuit x) (hy : NonConstCircuit y) :
    NonConstCircuit (smartAnd x y) := by
  cases x <;> cases y <;>
    simp_all [NonConstCircuit, smartAnd]

private theorem occurs_smartOr_left
    (v : Nat) (x y : Circuit)
    (hx : NonConstCircuit x) (hy : NonConstCircuit y)
    (ho : OccursInput v x) :
    OccursInput v (smartOr x y) := by
  cases x <;> cases y <;>
    simp_all [NonConstCircuit, OccursInput, smartOr]

private theorem occurs_smartOr_right
    (v : Nat) (x y : Circuit)
    (hx : NonConstCircuit x) (hy : NonConstCircuit y)
    (ho : OccursInput v y) :
    OccursInput v (smartOr x y) := by
  cases x <;> cases y <;>
    simp_all [NonConstCircuit, OccursInput, smartOr]

private theorem occurs_smartAnd_left
    (v : Nat) (x y : Circuit)
    (hx : NonConstCircuit x) (hy : NonConstCircuit y)
    (ho : OccursInput v x) :
    OccursInput v (smartAnd x y) := by
  cases x <;> cases y <;>
    simp_all [NonConstCircuit, OccursInput, smartAnd]

private theorem occurs_smartAnd_right
    (v : Nat) (x y : Circuit)
    (hx : NonConstCircuit x) (hy : NonConstCircuit y)
    (ho : OccursInput v y) :
    OccursInput v (smartAnd x y) := by
  cases x <;> cases y <;>
    simp_all [NonConstCircuit, OccursInput, smartAnd]

private theorem clauseCircuitNorm_nonconst
    (c : Clause) (hne : c ≠ []) :
    NonConstCircuit (clauseCircuitNorm c) := by
  induction c with
  | nil => exact False.elim (hne rfl)
  | cons l ls ih =>
      cases ls with
      | nil =>
          simpa [clauseCircuitNorm] using literalCircuit_nonconst l
      | cons l2 ls2 =>
          exact smartOr_nonconst
            (literalCircuit l) (clauseCircuitNorm (l2 :: ls2))
            (literalCircuit_nonconst l)
            (ih (by simp))

private theorem occurs_clauseCircuitNorm_of_mem
    (v : Nat) (c : Clause) (hne : c ≠ [])
    {l : Literal} (hl : l ∈ c) (hvar : l.var = v) :
    OccursInput v (clauseCircuitNorm c) := by
  induction c with
  | nil => simp at hl
  | cons a as ih =>
      simp only [List.mem_cons] at hl
      cases as with
      | nil =>
          have hal : l = a := by
            cases hl with
            | inl h => exact h
            | inr h => simp at h
          subst l
          simpa [clauseCircuitNorm, hvar] using occurs_literalCircuit_self a
      | cons b bs =>
          have htailne : (b :: bs) ≠ [] := by simp
          have hleftnc := literalCircuit_nonconst a
          have hrightnc := clauseCircuitNorm_nonconst (b :: bs) htailne
          cases hl with
          | inl hal =>
              subst l
              exact occurs_smartOr_left v
                (literalCircuit a) (clauseCircuitNorm (b :: bs))
                hleftnc hrightnc
                (by simpa [hvar] using occurs_literalCircuit_self a)
          | inr htail =>
              exact occurs_smartOr_right v
                (literalCircuit a) (clauseCircuitNorm (b :: bs))
                hleftnc hrightnc
                (ih htailne htail)

private theorem cnfCircuitNorm_nonconst
    (f : CNF)
    (hfn : f ≠ [])
    (hne : ∀ c : Clause, c ∈ f → c ≠ []) :
    NonConstCircuit (cnfCircuitNorm f) := by
  induction f with
  | nil =>
      exact False.elim (hfn rfl)
  | cons c cs ih =>
      cases cs with
      | nil =>
          simpa [cnfCircuitNorm] using clauseCircuitNorm_nonconst c (hne c (by simp))
      | cons c2 cs2 =>
          have hc : NonConstCircuit (clauseCircuitNorm c) :=
            clauseCircuitNorm_nonconst c (hne c (by simp))
          have htail : ∀ d : Clause, d ∈ (c2 :: cs2) → d ≠ [] := by
            intro d hd
            exact hne d (by simp [hd])
          exact smartAnd_nonconst
            (clauseCircuitNorm c) (cnfCircuitNorm (c2 :: cs2))
            hc (ih (by simp) htail)

private theorem occurs_cnfCircuitNorm_of_mem
    (v : Nat) (f : CNF)
    (hne : ∀ c : Clause, c ∈ f → c ≠ [])
    {c : Clause} (hc : c ∈ f)
    {l : Literal} (hl : l ∈ c) (hvar : l.var = v) :
    OccursInput v (cnfCircuitNorm f) := by
  induction f with
  | nil => simp at hc
  | cons d ds ih =>
      simp only [List.mem_cons] at hc
      cases ds with
      | nil =>
          have hcd : c = d := by
            cases hc with
            | inl h => exact h
            | inr h => simp at h
          subst c
          simpa [cnfCircuitNorm] using
            occurs_clauseCircuitNorm_of_mem v d (hne d (by simp)) hl hvar
      | cons d2 ds2 =>
          have hdnc : NonConstCircuit (clauseCircuitNorm d) :=
            clauseCircuitNorm_nonconst d (hne d (by simp))
          have htail : ∀ e : Clause, e ∈ (d2 :: ds2) → e ≠ [] := by
            intro e he
            exact hne e (by simp [he])
          have htailnc : NonConstCircuit (cnfCircuitNorm (d2 :: ds2)) :=
            cnfCircuitNorm_nonconst (d2 :: ds2) (by simp) htail
          cases hc with
          | inl hcd =>
              subst c
              exact occurs_smartAnd_left v
                (clauseCircuitNorm d) (cnfCircuitNorm (d2 :: ds2))
                hdnc htailnc
                (occurs_clauseCircuitNorm_of_mem v d (hne d (by simp)) hl hvar)
          | inr hctail =>
              exact occurs_smartAnd_right v
                (clauseCircuitNorm d) (cnfCircuitNorm (d2 :: ds2))
                hdnc htailnc
                (ih htail hctail)

private theorem map_or_imp
    {P Q P' Q' : Prop}
    (hp : P → P') (hq : Q → Q') :
    P ∨ Q → P' ∨ Q' := by
  intro h
  cases h with
  | inl hp0 => exact Or.inl (hp hp0)
  | inr hq0 => exact Or.inr (hq hq0)

private theorem occurs_simplify_imp
    (v : Nat) (t : Circuit) :
    OccursInput v (MCore.CircuitC2.simplify t) → OccursInput v t := by
  induction t with
  | input i =>
      simp [MCore.CircuitC2.simplify, OccursInput]
  | const b =>
      simp [MCore.CircuitC2.simplify, OccursInput]
  | not t ih =>
      simp only [MCore.CircuitC2.simplify]
      cases h : MCore.CircuitC2.simplify t with
      | input i => simp_all [OccursInput]
      | const cb => cases cb <;> simp_all [OccursInput]
      | not c => simp_all [OccursInput]
      | and c d => simp_all [OccursInput]
      | or c d => simp_all [OccursInput]
  | and a b iha ihb =>
      simp only [MCore.CircuitC2.simplify]
      cases ha : MCore.CircuitC2.simplify a with
      | input ia =>
          cases hb : MCore.CircuitC2.simplify b with
          | input ib =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | const cb =>
              cases cb <;> simp_all [OccursInput]
          | not c =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | and c d =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | or c d =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
      | const ca =>
          cases ca <;>
            cases hb : MCore.CircuitC2.simplify b with
            | input ib => simp_all [OccursInput]
            | const cb => cases cb <;> simp_all [OccursInput]
            | not c => simp_all [OccursInput]
            | and c d => simp_all [OccursInput]
            | or c d => simp_all [OccursInput]
      | not c =>
          cases hb : MCore.CircuitC2.simplify b with
          | input ib =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | const cb =>
              cases cb <;> simp_all [OccursInput]
          | not d =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | and d e =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | or d e =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
      | and c d =>
          cases hb : MCore.CircuitC2.simplify b with
          | input ib =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | const cb =>
              cases cb <;> simp_all [OccursInput]
          | not e =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | and e f =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | or e f =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
      | or c d =>
          cases hb : MCore.CircuitC2.simplify b with
          | input ib =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | const cb =>
              cases cb <;> simp_all [OccursInput]
          | not e =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | and e f =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | or e f =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
  | or a b iha ihb =>
      simp only [MCore.CircuitC2.simplify]
      cases ha : MCore.CircuitC2.simplify a with
      | input ia =>
          cases hb : MCore.CircuitC2.simplify b with
          | input ib =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | const cb =>
              cases cb <;> simp_all [OccursInput]
          | not c =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | and c d =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | or c d =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
      | const ca =>
          cases ca <;>
            cases hb : MCore.CircuitC2.simplify b with
            | input ib => simp_all [OccursInput]
            | const cb => cases cb <;> simp_all [OccursInput]
            | not c => simp_all [OccursInput]
            | and c d => simp_all [OccursInput]
            | or c d => simp_all [OccursInput]
      | not c =>
          cases hb : MCore.CircuitC2.simplify b with
          | input ib =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | const cb =>
              cases cb <;> simp_all [OccursInput]
          | not d =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | and d e =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | or d e =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
      | and c d =>
          cases hb : MCore.CircuitC2.simplify b with
          | input ib =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | const cb =>
              cases cb <;> simp_all [OccursInput]
          | not e =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | and e f =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | or e f =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
      | or c d =>
          cases hb : MCore.CircuitC2.simplify b with
          | input ib =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | const cb =>
              cases cb <;> simp_all [OccursInput]
          | not e =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | and e f =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')
          | or e f =>
              intro h
              rcases h with h | h
              · have h' : OccursInput v (MCore.CircuitC2.simplify a) := by
                  simpa [ha, OccursInput] using h
                exact Or.inl (iha h')
              · have h' : OccursInput v (MCore.CircuitC2.simplify b) := by
                  simpa [hb, OccursInput] using h
                exact Or.inr (ihb h')

private theorem fixed_var_not_occurs_restrict
    (ρ : Restriction) (v : Nat) (t : Circuit)
    (hfixed : ρ v ≠ none) :
    ¬ OccursInput v (MCore.CircuitK1.restrict ρ t) := by
  induction t with
  | input i =>
      cases hri : ρ i with
      | none =>
          intro ho
          have hiv : i = v := by
            simpa [MCore.CircuitK1.restrict, hri, OccursInput] using ho
          subst i
          exact hfixed hri
      | some b =>
          simp [MCore.CircuitK1.restrict, hri, OccursInput]
  | const b =>
      simp [MCore.CircuitK1.restrict, OccursInput]
  | not t ih =>
      simpa [MCore.CircuitK1.restrict, OccursInput] using ih
  | and a b iha ihb =>
      simp [MCore.CircuitK1.restrict, OccursInput, iha, ihb]
  | or a b iha ihb =>
      simp [MCore.CircuitK1.restrict, OccursInput, iha, ihb]

private theorem coverageCore_clauses_nonempty
    (payload : CNF) :
    ∀ c : Clause, c ∈ coverageCore payload → c ≠ [] := by
  intro c hc
  simp only [coverageCore, List.mem_flatMap] at hc
  rcases hc with ⟨vi, _hvi, hc⟩
  simp [coverageClauses] at hc
  rcases hc with rfl | rfl <;> simp

private theorem restricted_core_var_implies_core_progress
    (ρ : Restriction) (payload : CNF) (v : Nat)
    (hvcore : v ∈ cnfVarList (coverageCore payload))
    (hfixed : ρ v ≠ none) :
    RestrictionProgressNorm ρ (cnfCircuitNorm (coverageCore payload)) := by
  have hvraw :
      v ∈ ((coverageCore payload).flatMap fun clause => clause.map Literal.var) :=
    Claim7VariableCoverage.mem_eraseDups_iff.mp hvcore
  simp only [List.mem_flatMap, List.mem_map] at hvraw
  rcases hvraw with ⟨c, hc, l, hl, hvar⟩
  have horig : OccursInput v (cnfCircuitNorm (coverageCore payload)) :=
    occurs_cnfCircuitNorm_of_mem v (coverageCore payload)
      (coverageCore_clauses_nonempty payload) hc hl hvar
  intro heq
  have hsimp :
      MCore.CircuitC2.simplify (cnfCircuitNorm (coverageCore payload)) =
        cnfCircuitNorm (coverageCore payload) :=
    simplify_cnfCircuitNorm_idem (coverageCore payload)
  have hres :
      DNorm ρ (cnfCircuitNorm (coverageCore payload)) =
        cnfCircuitNorm (coverageCore payload) := by
    exact heq.trans hsimp
  have hoccD : OccursInput v (DNorm ρ (cnfCircuitNorm (coverageCore payload))) := by
    rw [hres]
    exact horig
  unfold DNorm at hoccD
  have hoccRestrict :
      OccursInput v
        (MCore.CircuitK1.restrict ρ
          (MCore.CircuitC2.simplify (cnfCircuitNorm (coverageCore payload)))) :=
    occurs_simplify_imp v
      (MCore.CircuitK1.restrict ρ
        (MCore.CircuitC2.simplify (cnfCircuitNorm (coverageCore payload))))
      hoccD
  exact (fixed_var_not_occurs_restrict ρ v
    (MCore.CircuitC2.simplify (cnfCircuitNorm (coverageCore payload))) hfixed)
    hoccRestrict

/-- TARGET2c: restricting any payload variable forces normalized progress in its coverage core. -/
theorem restricted_coverage_var_implies_core_progress
    (ρ : Restriction) (payload : CNF) (v : Nat)
    (hv : v ∈ cnfVarList payload)
    (hfixed : ρ v ≠ none) :
    RestrictionProgressNorm ρ (cnfCircuitNorm (coverageCore payload)) := by
  exact restricted_core_var_implies_core_progress ρ payload v
    (payload_var_mem_coverageCore hv) hfixed

#print axioms MCore.Real.P02Lane4TotalVariableCoverageNorm.restricted_coverage_var_implies_core_progress

private theorem cnfVarList_append_mem_split
    {a b : CNF} {v : Nat}
    (hv : v ∈ cnfVarList (a ++ b)) :
    v ∈ cnfVarList a ∨ v ∈ cnfVarList b := by
  have hraw :
      v ∈ ((a ++ b).flatMap fun clause => clause.map Literal.var) :=
    Claim7VariableCoverage.mem_eraseDups_iff.mp hv
  rw [List.flatMap_append] at hraw
  rcases List.mem_append.mp hraw with ha | hb
  · exact Or.inl (Claim7VariableCoverage.mem_eraseDups_iff.mpr ha)
  · exact Or.inr (Claim7VariableCoverage.mem_eraseDups_iff.mpr hb)

/-- TARGET3: progress on payload ++ coverageCore forces progress on coverageCore. -/
theorem coverageCore_progress_of_padded_progress
    (ρ : Restriction) (payload : CNF)
    (hpad :
      RestrictionProgressNorm ρ
        (cnfCircuitNorm (payload ++ coverageCore payload))) :
    RestrictionProgressNorm ρ (cnfCircuitNorm (coverageCore payload)) := by
  obtain ⟨v, hv, hfixed⟩ :=
    progressNorm_implies_restricted_var ρ
      (payload ++ coverageCore payload) hpad
  rcases cnfVarList_append_mem_split hv with hvPayload | hvCore
  · exact restricted_coverage_var_implies_core_progress
      ρ payload v hvPayload hfixed
  · exact restricted_core_var_implies_core_progress
      ρ payload v hvCore hfixed

#print axioms MCore.Real.P02Lane4TotalVariableCoverageNorm.coverageCore_progress_of_padded_progress

/-- Normalized core-aware progress. Both payload+core and core are measured only
after canonical normalization, so representation-only simplification is excluded. -/
def CoreAwareProgressNorm
    (ρ : Restriction)
    (payload core : CNF) : Prop :=
  RestrictionProgressNorm ρ (cnfCircuitNorm (payload ++ core)) ∧
  RestrictionProgressNorm ρ (cnfCircuitNorm core)

/-- Exact normalized coverage obligation for a payload/core pair. -/
def CoreAwareProgressCoverageNorm
    (payload core : CNF) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgressNorm ρ (cnfCircuitNorm (payload ++ core)) →
      CoreAwareProgressNorm ρ payload core

/-- Terminal normalized coverage obligation for the total-variable gadget.
This is deliberately a proposition only: this file does not postulate or
manufacture an inhabitant. -/
def TotalVariableCoverageObligationNorm
    (payload : CNF) : Prop :=
  CoreAwareProgressCoverageNorm payload (coverageCore payload)

theorem totalVariableCoverageObligationNorm_unfold
    (payload : CNF) :
    TotalVariableCoverageObligationNorm payload ↔
      ∀ ρ : Restriction,
        RestrictionProgressNorm ρ
          (cnfCircuitNorm (payload ++ coverageCore payload)) →
        CoreAwareProgressNorm ρ payload (coverageCore payload) := by
  rfl

#print axioms MCore.Real.P02Lane4TotalVariableCoverageNorm.totalVariableCoverageObligationNorm_unfold


/-- TARGET4: the total-variable coverage obligation is inhabited by the TARGET3 bridge. -/
theorem totalVariableCoverageObligationNorm
    (payload : CNF) :
    TotalVariableCoverageObligationNorm payload := by
  unfold TotalVariableCoverageObligationNorm
  unfold CoreAwareProgressCoverageNorm
  intro ρ hpad
  unfold CoreAwareProgressNorm
  exact ⟨hpad, coverageCore_progress_of_padded_progress ρ payload hpad⟩

#print axioms MCore.Real.P02Lane4TotalVariableCoverageNorm.totalVariableCoverageObligationNorm

end P02Lane4TotalVariableCoverageNorm
end Real
end MCore
