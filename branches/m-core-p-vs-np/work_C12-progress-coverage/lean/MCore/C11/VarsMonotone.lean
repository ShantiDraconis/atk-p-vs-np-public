import Init.Data.List.Erase
import Init.Data.List.Lemmas
import Init.Data.List.Pairwise
import MCore.C10.RestrictionProgress

namespace MCore
namespace C11

open C9 C10 CircuitK1 CircuitC2

/-- Membership invariant for the Lean 4.19 implementation of `List.eraseDups`.
The accumulator and unprocessed input contain exactly the elements that can
appear in the final output. -/
theorem eraseDups_loop_mem_nat (x : Nat) :
    ∀ (as bs : List Nat),
      x ∈ List.eraseDups.loop as bs ↔ x ∈ as ∨ x ∈ bs := by
  intro as
  induction as with
  | nil =>
      intro bs
      simp [List.eraseDups.loop]
  | cons a as ih =>
      intro bs
      cases h : bs.elem a with
      | false =>
          simp only [List.eraseDups.loop, h]
          rw [ih]
          simp only [List.mem_cons]
          constructor
          · intro hout
            rcases hout with hxas | hxab
            · exact Or.inl (Or.inr hxas)
            · rcases hxab with hxa | hxbs
              · exact Or.inl (Or.inl hxa)
              · exact Or.inr hxbs
          · intro hin
            rcases hin with hxaas | hxbs
            · rcases hxaas with hxa | hxas
              · exact Or.inr (Or.inl hxa)
              · exact Or.inl hxas
            · exact Or.inr (Or.inr hxbs)
      | true =>
          have ha : a ∈ bs := (List.elem_iff).1 h
          simp only [List.eraseDups.loop, h]
          rw [ih]
          simp only [List.mem_cons]
          constructor
          · intro hout
            rcases hout with hxas | hxbs
            · exact Or.inl (Or.inr hxas)
            · exact Or.inr hxbs
          · intro hin
            rcases hin with hxaas | hxbs
            · rcases hxaas with hxa | hxas
              · have hxab : x ∈ bs := by
                  rw [hxa]
                  exact ha
                exact Or.inr hxab
              · exact Or.inl hxas
            · exact Or.inr hxbs

/-- The Lean 4.19 `eraseDups` loop preserves duplicate-freedom of its
accumulator. -/
theorem eraseDups_loop_nodup_nat :
    ∀ (as bs : List Nat), bs.Nodup → (List.eraseDups.loop as bs).Nodup := by
  intro as
  induction as with
  | nil =>
      intro bs hbs
      simp only [List.eraseDups.loop]
      unfold List.Nodup at hbs ⊢
      rw [List.pairwise_reverse]
      simpa [ne_comm] using hbs
  | cons a as ih =>
      intro bs hbs
      cases h : bs.elem a with
      | false =>
          have ha : a ∉ bs := by
            intro ham
            have ht : bs.elem a = true := (List.elem_iff).2 ham
            rw [h] at ht
            exact Bool.noConfusion ht
          simp only [List.eraseDups.loop, h]
          apply ih
          exact (List.nodup_cons).2 ⟨ha, hbs⟩
      | true =>
          simp only [List.eraseDups.loop, h]
          exact ih bs hbs

theorem mem_eraseDups_nat {x : Nat} {l : List Nat} :
    x ∈ l.eraseDups ↔ x ∈ l := by
  simpa [List.eraseDups] using eraseDups_loop_mem_nat x l []

theorem eraseDups_nodup_nat (l : List Nat) : l.eraseDups.Nodup := by
  simpa [List.eraseDups] using
    (eraseDups_loop_nodup_nat l [] List.nodup_nil)

/-- Lean 4.19 lacks the later-library theorem
`Nodup.length_le_of_subset`; this is the local compatible version. -/
theorem nodup_length_le_of_subset_nat
    {l₁ l₂ : List Nat}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hsub : l₁ ⊆ l₂) :
    l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil =>
      simp
  | cons a t ih =>
      have hnod : a ∉ t ∧ t.Nodup := (List.nodup_cons).1 h₁
      have ha : a ∈ l₂ := hsub (by simp)
      have hsubt : t ⊆ l₂.erase a := by
        intro x hx
        have hxa : x ≠ a := by
          intro hxa
          subst x
          exact hnod.1 hx
        exact (List.mem_erase_of_ne hxa).2 (hsub (by simp [hx]))
      have h₂erase : (l₂.erase a).Nodup := by
        exact List.Pairwise.erase a h₂
      have hih := ih hnod.2 h₂erase hsubt
      have hlen : (l₂.erase a).length = l₂.length - 1 :=
        List.length_erase_of_mem ha
      simp only [List.length_cons]
      rw [hlen] at hih
      have hpos : 1 ≤ l₂.length := List.length_pos_of_mem ha
      omega

theorem eraseDups_length_le_of_subset
    {l₁ l₂ : List Nat} (h : l₁ ⊆ l₂) :
    l₁.eraseDups.length ≤ l₂.eraseDups.length := by
  apply nodup_length_le_of_subset_nat
      (eraseDups_nodup_nat l₁) (eraseDups_nodup_nat l₂)
  intro x hx
  apply (mem_eraseDups_nat).2
  apply h
  exact (mem_eraseDups_nat).1 hx

/-- Restriction can replace an input by a constant, but cannot introduce a new
syntactic input identifier. -/
theorem mem_freeVarList_restrict
    {x : Nat} (ρ : Restriction) (t : FormulaTree)
    (hx : x ∈ freeVarList (restrict ρ t)) :
    x ∈ freeVarList t := by
  induction t with
  | input i =>
      cases h : ρ i <;> simp [restrict, freeVarList, h] at hx ⊢
      exact hx
  | const b =>
      simp [restrict, freeVarList] at hx
  | not c ih =>
      exact ih (by simpa [restrict, freeVarList] using hx)
  | and a b iha ihb =>
      simp [restrict, freeVarList] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (iha hx)
      · exact Or.inr (ihb hx)
  | or a b iha ihb =>
      simp [restrict, freeVarList] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (iha hx)
      · exact Or.inr (ihb hx)

/-- Proof-friendly local mirrors of the three simplifier constructors. -/
def reduceNot : FormulaTree → FormulaTree
  | .const b => .const (!b)
  | d => .not d

def reduceAnd : FormulaTree → FormulaTree → FormulaTree
  | .const false, _ => .const false
  | _, .const false => .const false
  | .const true, d => d
  | d, .const true => d
  | d, e => .and d e

def reduceOr : FormulaTree → FormulaTree → FormulaTree
  | .const true, _ => .const true
  | _, .const true => .const true
  | .const false, d => d
  | d, .const false => d
  | d, e => .or d e

@[simp] theorem simplify_not_eq (c : FormulaTree) :
    simplify (.not c) = reduceNot (simplify c) := rfl

@[simp] theorem simplify_and_eq (a b : FormulaTree) :
    simplify (.and a b) = reduceAnd (simplify a) (simplify b) := rfl

@[simp] theorem simplify_or_eq (a b : FormulaTree) :
    simplify (.or a b) = reduceOr (simplify a) (simplify b) := rfl

theorem mem_freeVarList_reduceNot
    {x : Nat} {d : FormulaTree}
    (hx : x ∈ freeVarList (reduceNot d)) :
    x ∈ freeVarList d := by
  cases d
  all_goals try cases ‹Bool›
  all_goals simp_all [reduceNot, freeVarList]

theorem mem_freeVarList_reduceAnd
    {x : Nat} {d e : FormulaTree}
    (hx : x ∈ freeVarList (reduceAnd d e)) :
    x ∈ freeVarList d ∨ x ∈ freeVarList e := by
  cases d <;> cases e
  all_goals try cases ‹Bool›
  all_goals try cases ‹Bool›
  all_goals simp_all [reduceAnd, freeVarList, or_assoc]

theorem mem_freeVarList_reduceOr
    {x : Nat} {d e : FormulaTree}
    (hx : x ∈ freeVarList (reduceOr d e)) :
    x ∈ freeVarList d ∨ x ∈ freeVarList e := by
  cases d <;> cases e
  all_goals try cases ‹Bool›
  all_goals try cases ‹Bool›
  all_goals simp_all [reduceOr, freeVarList, or_assoc]

/-- The certified simplifier can delete branches and constants, but cannot
invent a new syntactic input identifier. -/
theorem mem_freeVarList_simplify
    {x : Nat} (t : FormulaTree)
    (hx : x ∈ freeVarList (simplify t)) :
    x ∈ freeVarList t := by
  induction t with
  | input i =>
      simpa [simplify, freeVarList] using hx
  | const b =>
      simp [simplify, freeVarList] at hx
  | not c ih =>
      apply ih
      apply mem_freeVarList_reduceNot
      simpa [simplify_not_eq] using hx
  | and a b iha ihb =>
      have hchildren :
          x ∈ freeVarList (simplify a) ∨
          x ∈ freeVarList (simplify b) := by
        apply mem_freeVarList_reduceAnd
        simpa [simplify_and_eq] using hx
      rcases hchildren with ha | hb
      · simp [freeVarList]
        exact Or.inl (iha ha)
      · simp [freeVarList]
        exact Or.inr (ihb hb)
  | or a b iha ihb =>
      have hchildren :
          x ∈ freeVarList (simplify a) ∨
          x ∈ freeVarList (simplify b) := by
        apply mem_freeVarList_reduceOr
        simpa [simplify_or_eq] using hx
      rcases hchildren with ha | hb
      · simp [freeVarList]
        exact Or.inl (iha ha)
      · simp [freeVarList]
        exact Or.inr (ihb hb)

/-- The full C9 map `D = simplify ∘ restrict` never introduces a free variable. -/
theorem mem_freeVarList_D
    {x : Nat} (ρ : Restriction) (t : FormulaTree)
    (hx : x ∈ freeVarList (D ρ t)) :
    x ∈ freeVarList t := by
  have hs : x ∈ freeVarList (restrict ρ t) := by
    apply mem_freeVarList_simplify (restrict ρ t)
    simpa [D] using hx
  exact mem_freeVarList_restrict ρ t hs

/-- C11 closes the first C10 bridge: the number of distinct syntactic variables
is globally nonincreasing under restriction followed by simplification. -/
theorem vars_D_le (ρ : Restriction) (t : FormulaTree) :
    vars (D ρ t) ≤ vars t := by
  unfold vars
  apply eraseDups_length_le_of_subset
  intro x hx
  exact mem_freeVarList_D ρ t hx

theorem varsNonincrease_closed : VarsNonincreaseObligation := by
  intro ρ t
  exact vars_D_le ρ t

/-- After C11, C10's rank theorem needs only strict progress: either a strict
variable-count decrease or positive certified potential decrement. -/
def StrictRestrictionProgress (ρ : Restriction) (t : FormulaTree) : Prop :=
  vars (D ρ t) < vars t ∨ 0 < delta ρ t

theorem restrictionProgress_of_strict
    (ρ : Restriction) (t : FormulaTree)
    (h : StrictRestrictionProgress ρ t) :
    RestrictionProgress ρ t :=
  ⟨vars_D_le ρ t, h⟩

theorem stateRank_D_decreases_of_strict
    (ρ : Restriction) (t : FormulaTree)
    (h : StrictRestrictionProgress ρ t) :
    stateRank (D ρ t) < stateRank t :=
  stateRank_D_decreases_of_restriction_progress
    ρ t (restrictionProgress_of_strict ρ t h)

theorem c11_classical_endpoint_not_promoted :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c10_classical_endpoint_not_promoted

theorem c11_k10_not_promoted :
    ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c10_k10_not_promoted

end C11
end MCore
