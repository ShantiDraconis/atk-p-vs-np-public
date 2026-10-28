import MCore.CircuitK1

namespace MCore
namespace CircuitC2

open CircuitK1

abbrev Assignment := Nat → Bool

def eval (σ : Assignment) : Circuit → Bool
  | .input i => σ i
  | .const b => b
  | .not c => !(eval σ c)
  | .and a b => (eval σ a) && (eval σ b)
  | .or a b => (eval σ a) || (eval σ b)

def merge (ρ : Restriction) (σ : Assignment) : Assignment := fun i =>
  match ρ i with
  | some b => b
  | none => σ i

@[simp] theorem merge_some (ρ : Restriction) (σ : Assignment) (i : Nat) (b : Bool)
    (h : ρ i = some b) : merge ρ σ i = b := by simp [merge, h]

@[simp] theorem merge_none (ρ : Restriction) (σ : Assignment) (i : Nat)
    (h : ρ i = none) : merge ρ σ i = σ i := by simp [merge, h]

theorem eval_restrict (ρ : Restriction) (σ : Assignment) (c : Circuit) :
    eval σ (restrict ρ c) = eval (merge ρ σ) c := by
  induction c with
  | input i => cases h : ρ i <;> simp [restrict, eval, merge, h]
  | const b => rfl
  | not c ih => simp [restrict, eval, ih]
  | and a b iha ihb => simp [restrict, eval, iha, ihb]
  | or a b iha ihb => simp [restrict, eval, iha, ihb]

def simplifyAnd : Circuit → Circuit → Circuit
  | .const false, _ => .const false
  | _, .const false => .const false
  | .const true, d => d
  | d, .const true => d
  | d, e => .and d e

def simplifyOr : Circuit → Circuit → Circuit
  | .const true, _ => .const true
  | _, .const true => .const true
  | .const false, d => d
  | d, .const false => d
  | d, e => .or d e

def simplify : Circuit → Circuit
  | .input i => .input i
  | .const b => .const b
  | .not c =>
      match simplify c with
      | .const b => .const (!b)
      | d => .not d
  | .and a b => simplifyAnd (simplify a) (simplify b)
  | .or a b => simplifyOr (simplify a) (simplify b)

/-- Local conjunction folding never exceeds the unfurled parent size. -/
theorem size_simplifyAnd_le (a b : Circuit) :
    size (simplifyAnd a b) ≤ size a + size b + 1 := by
  cases a with
  | input i => cases b <;> simp [simplifyAnd, size] <;> omega
  | const ba =>
      cases ba <;> cases b with
      | input i => simp [simplifyAnd, size]
      | const bb => cases bb <;> simp [simplifyAnd, size]
      | not c => simp [simplifyAnd, size]
      | and c d => simp [simplifyAnd, size]
      | or c d => simp [simplifyAnd, size]
  | not c => cases b <;> simp [simplifyAnd, size] <;> omega
  | and c d => cases b <;> simp [simplifyAnd, size] <;> omega
  | or c d => cases b <;> simp [simplifyAnd, size] <;> omega

/-- Local disjunction folding never exceeds the unfurled parent size. -/
theorem size_simplifyOr_le (a b : Circuit) :
    size (simplifyOr a b) ≤ size a + size b + 1 := by
  cases a with
  | input i => cases b <;> simp [simplifyOr, size] <;> omega
  | const ba =>
      cases ba <;> cases b with
      | input i => simp [simplifyOr, size]
      | const bb => cases bb <;> simp [simplifyOr, size]
      | not c => simp [simplifyOr, size]
      | and c d => simp [simplifyOr, size]
      | or c d => simp [simplifyOr, size]
  | not c => cases b <;> simp [simplifyOr, size] <;> omega
  | and c d => cases b <;> simp [simplifyOr, size] <;> omega
  | or c d => cases b <;> simp [simplifyOr, size] <;> omega

/-- Local conjunction folding never exceeds the unfurled parent depth. -/
theorem depth_simplifyAnd_le (a b : Circuit) :
    depth (simplifyAnd a b) ≤ max (depth a) (depth b) + 1 := by
  cases a with
  | input i => cases b <;> simp [simplifyAnd, depth] <;> omega
  | const ba =>
      cases ba <;> cases b with
      | input i => simp [simplifyAnd, depth]
      | const bb => cases bb <;> simp [simplifyAnd, depth]
      | not c => simp [simplifyAnd, depth]
      | and c d => simp [simplifyAnd, depth]
      | or c d => simp [simplifyAnd, depth]
  | not c => cases b <;> simp [simplifyAnd, depth] <;> omega
  | and c d => cases b <;> simp [simplifyAnd, depth] <;> omega
  | or c d => cases b <;> simp [simplifyAnd, depth] <;> omega

/-- Local disjunction folding never exceeds the unfurled parent depth. -/
theorem depth_simplifyOr_le (a b : Circuit) :
    depth (simplifyOr a b) ≤ max (depth a) (depth b) + 1 := by
  cases a with
  | input i => cases b <;> simp [simplifyOr, depth] <;> omega
  | const ba =>
      cases ba <;> cases b with
      | input i => simp [simplifyOr, depth]
      | const bb => cases bb <;> simp [simplifyOr, depth]
      | not c => simp [simplifyOr, depth]
      | and c d => simp [simplifyOr, depth]
      | or c d => simp [simplifyOr, depth]
  | not c => cases b <;> simp [simplifyOr, depth] <;> omega
  | and c d => cases b <;> simp [simplifyOr, depth] <;> omega
  | or c d => cases b <;> simp [simplifyOr, depth] <;> omega

/-- Simplification never increases formula-tree size. -/
theorem size_simplify_le (c : Circuit) : size (simplify c) ≤ size c := by
  induction c with
  | input i => simp [simplify, size]
  | const b => simp [simplify, size]
  | not c ih =>
      simp only [simplify]
      cases h : simplify c <;> simp_all [size]
  | and a b iha ihb =>
      simp only [simplify, size]
      exact Nat.le_trans (size_simplifyAnd_le (simplify a) (simplify b))
        (Nat.add_le_add_right (Nat.add_le_add iha ihb) 1)
  | or a b iha ihb =>
      simp only [simplify, size]
      exact Nat.le_trans (size_simplifyOr_le (simplify a) (simplify b))
        (Nat.add_le_add_right (Nat.add_le_add iha ihb) 1)

/-- Simplification never increases formula-tree depth. -/
theorem depth_simplify_le (c : Circuit) : depth (simplify c) ≤ depth c := by
  induction c with
  | input i => simp [simplify, depth]
  | const b => simp [simplify, depth]
  | not c ih =>
      simp only [simplify]
      cases h : simplify c <;> simp_all [depth] <;> omega
  | and a b iha ihb =>
      simp only [simplify, depth]
      exact Nat.le_trans (depth_simplifyAnd_le (simplify a) (simplify b))
        (Nat.add_le_add_right (max_le_max iha ihb) 1)
  | or a b iha ihb =>
      simp only [simplify, depth]
      exact Nat.le_trans (depth_simplifyOr_le (simplify a) (simplify b))
        (Nat.add_le_add_right (max_le_max iha ihb) 1)

/-- The C1 structural potential is monotone under simplification. -/
theorem μ_simplify_le (c : Circuit) : μ (simplify c) ≤ μ c := by
  unfold μ
  exact Nat.add_le_add (size_simplify_le c) (depth_simplify_le c)

/-- Local conjunction folding preserves Boolean semantics. -/
theorem eval_simplifyAnd (σ : Assignment) (a b : Circuit) :
    eval σ (simplifyAnd a b) = (eval σ a && eval σ b) := by
  cases a with
  | input i => cases b <;> simp [simplifyAnd, eval] <;> split <;> simp_all [eval]
  | const ba =>
      cases ba <;> cases b with
      | input i => simp [simplifyAnd, eval]
      | const bb => cases bb <;> simp [simplifyAnd, eval]
      | not c => simp [simplifyAnd, eval]
      | and c d => simp [simplifyAnd, eval]
      | or c d => simp [simplifyAnd, eval]
  | not c => cases b <;> simp [simplifyAnd, eval] <;> split <;> simp_all [eval]
  | and c d => cases b <;> simp [simplifyAnd, eval] <;> split <;> simp_all [eval]
  | or c d => cases b <;> simp [simplifyAnd, eval] <;> split <;> simp_all [eval]

/-- Local disjunction folding preserves Boolean semantics. -/
theorem eval_simplifyOr (σ : Assignment) (a b : Circuit) :
    eval σ (simplifyOr a b) = (eval σ a || eval σ b) := by
  cases a with
  | input i => cases b <;> simp [simplifyOr, eval] <;> split <;> simp_all [eval]
  | const ba =>
      cases ba <;> cases b with
      | input i => simp [simplifyOr, eval]
      | const bb => cases bb <;> simp [simplifyOr, eval]
      | not c => simp [simplifyOr, eval]
      | and c d => simp [simplifyOr, eval]
      | or c d => simp [simplifyOr, eval]
  | not c => cases b <;> simp [simplifyOr, eval] <;> split <;> simp_all [eval]
  | and c d => cases b <;> simp [simplifyOr, eval] <;> split <;> simp_all [eval]
  | or c d => cases b <;> simp [simplifyOr, eval] <;> split <;> simp_all [eval]

theorem eval_simplify (σ : Assignment) (c : Circuit) : eval σ (simplify c) = eval σ c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | not c ih =>
      simp only [simplify]
      cases h : simplify c with
      | input i => simp_all [eval]
      | const b => cases b <;> simp_all [eval]
      | not d => simp_all [eval]
      | and a b => simp_all [eval]
      | or a b => simp_all [eval]
  | and a b iha ihb =>
      simp only [simplify, eval]
      rw [eval_simplifyAnd, iha, ihb]
  | or a b iha ihb =>
      simp only [simplify, eval]
      rw [eval_simplifyOr, iha, ihb]

def restrictedSimplified (ρ : Restriction) (c : Circuit) : Circuit :=
  simplify (restrict ρ c)

theorem eval_restrictedSimplified (ρ : Restriction) (σ : Assignment) (c : Circuit) :
    eval σ (restrictedSimplified ρ c) = eval (merge ρ σ) c := by
  rw [restrictedSimplified, eval_simplify, eval_restrict]

end CircuitC2
end MCore
