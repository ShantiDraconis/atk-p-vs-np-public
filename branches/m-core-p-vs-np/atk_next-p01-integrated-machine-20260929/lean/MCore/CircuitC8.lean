import MCore.CircuitC7

namespace MCore
namespace CircuitC8

open CircuitK1 CircuitC2 CircuitC3 CircuitC4 CircuitC5 CircuitC6 CircuitC7

/-- C8-local proof: the certified C2 simplifier never increases formula size.
Kept here so the frozen C2 scientific object remains untouched. -/
theorem size_simplify_le_c8 (c : Circuit) : size (simplify c) ≤ size c := by
  induction c with
  | input i => simp [simplify, size]
  | const b => simp [simplify, size]
  | not c ih =>
      simp only [simplify]
      cases h : simplify c with
      | input i =>
          have hs : size (Circuit.input i) ≤ size c := by simpa [h] using ih
          simpa [size] using hs
      | const b => simp [size]
      | not d =>
          have hs : size (Circuit.not d) ≤ size c := by simpa [h] using ih
          simpa [size] using hs
      | and a b =>
          have hs : size (Circuit.and a b) ≤ size c := by simpa [h] using ih
          simpa [size] using hs
      | or a b =>
          have hs : size (Circuit.or a b) ≤ size c := by simpa [h] using ih
          simpa [size] using hs
  | and a b iha ihb =>
      simp only [simplify]
      cases ha : simplify a <;> cases hb : simplify b <;>
        (try split) <;> simp_all [size] <;> omega
  | or a b iha ihb =>
      simp only [simplify]
      cases ha : simplify a <;> cases hb : simplify b <;>
        (try split) <;> simp_all [size] <;> omega

/-- C8-local depth monotonicity for the certified C2 simplifier. -/
theorem depth_simplify_le_c8 (c : Circuit) : depth (simplify c) ≤ depth c := by
  induction c with
  | input i => simp [simplify, depth]
  | const b => simp [simplify, depth]
  | not c ih =>
      simp only [simplify]
      cases h : simplify c with
      | input i => simp [depth]
      | const b => simp [depth]
      | not d =>
          have hd : depth (Circuit.not d) ≤ depth c := by simpa [h] using ih
          simpa [depth] using hd
      | and a b =>
          have hd : depth (Circuit.and a b) ≤ depth c := by simpa [h] using ih
          simpa [depth] using hd
      | or a b =>
          have hd : depth (Circuit.or a b) ≤ depth c := by simpa [h] using ih
          simpa [depth] using hd
  | and a b iha ihb =>
      simp only [simplify]
      cases ha : simplify a <;> cases hb : simplify b <;>
        (try split) <;> simp_all [depth] <;> omega
  | or a b iha ihb =>
      simp only [simplify]
      cases ha : simplify a <;> cases hb : simplify b <;>
        (try split) <;> simp_all [depth] <;> omega

/-- Structural potential cannot increase under the certified simplifier. -/
theorem potential_simplify_le_c8 (c : Circuit) : potential (simplify c) ≤ potential c := by
  unfold potential μ
  exact Nat.add_le_add (size_simplify_le_c8 c) (depth_simplify_le_c8 c)

/-- Restriction itself preserves C1 potential, so restriction followed by
simplification is globally nonincreasing. This removes the Nat-subtraction
ambiguity inherited by C4-C7. -/
theorem potential_restrictedSimplified_le (ρ : Restriction) (c : Circuit) :
    potential (restrictedSimplified ρ c) ≤ potential c := by
  unfold restrictedSimplified
  have hs : potential (simplify (restrict ρ c)) ≤ potential (restrict ρ c) :=
    potential_simplify_le_c8 (restrict ρ c)
  have hr : potential (restrict ρ c) = potential c := by
    exact μ_restrict_invariant ρ c
  exact hr ▸ hs

/-- Exact accounting identity for C3's natural-number drop. -/
theorem restricted_potential_add_drop (ρ : Restriction) (c : Circuit) :
    potential (restrictedSimplified ρ c) + drop ρ c = potential c := by
  unfold drop
  exact Nat.add_sub_of_le (potential_restrictedSimplified_le ρ c)

/-- Under the proved nonincrease invariant, zero truncated drop means exact
potential equality rather than a masked increase. -/
theorem drop_eq_zero_iff (ρ : Restriction) (c : Circuit) :
    drop ρ c = 0 ↔ potential (restrictedSimplified ρ c) = potential c := by
  unfold drop
  constructor
  · intro h
    have hle := potential_restrictedSimplified_le ρ c
    omega
  · intro h
    simp [h]

/-- Positive drop is exactly C3 strict structural descent. -/
theorem drop_pos_iff_strict (ρ : Restriction) (c : Circuit) :
    0 < drop ρ c ↔ StrictDrop ρ c := by
  unfold drop StrictDrop
  have hle := potential_restrictedSimplified_le ρ c
  omega

structure RecurrenceBranch where
  fixedVars : Nat
  potentialDrop : Nat

def BranchProgress (b : RecurrenceBranch) : Prop :=
  0 < b.fixedVars ∨ 0 < b.potentialDrop

def recurrenceRank (vars potential : Nat) : Nat :=
  vars * (potential + 1) + potential

theorem rank_decreases_when_variable_fixed
    (vars potential fixedVars newPotential : Nat)
    (hfix : 0 < fixedVars) (hfixle : fixedVars ≤ vars)
    (hpot : newPotential ≤ potential) :
    recurrenceRank (vars - fixedVars) newPotential < recurrenceRank vars potential := by
  unfold recurrenceRank
  have hv : vars - fixedVars < vars := by omega
  have hmul : (vars - fixedVars) * (potential + 1) < vars * (potential + 1) :=
    Nat.mul_lt_mul_of_pos_right hv (Nat.succ_pos potential)
  have hleft : (vars - fixedVars) * (newPotential + 1) ≤
      (vars - fixedVars) * (potential + 1) :=
    Nat.mul_le_mul_left _ (Nat.succ_le_succ hpot)
  have hsum : (vars - fixedVars) * (newPotential + 1) + newPotential ≤
      (vars - fixedVars) * (potential + 1) + potential :=
    Nat.add_le_add hleft hpot
  have hstrict : (vars - fixedVars) * (potential + 1) + potential <
      vars * (potential + 1) + potential :=
    Nat.add_lt_add_right hmul potential
  exact Nat.lt_of_le_of_lt hsum hstrict

theorem rank_decreases_when_potential_drops
    (vars potential newPotential : Nat)
    (hpot : newPotential < potential) :
    recurrenceRank vars newPotential < recurrenceRank vars potential := by
  unfold recurrenceRank
  have hs : newPotential + 1 ≤ potential + 1 := Nat.succ_le_succ (Nat.le_of_lt hpot)
  have hm : vars * (newPotential + 1) ≤ vars * (potential + 1) :=
    Nat.mul_le_mul_left vars hs
  exact Nat.add_lt_add_of_le_of_lt hm hpot

theorem good_mass_supplies_aggregate_progress
    (sample : List WeightedRestriction) (c : Circuit)
    (minGoodWeight minDrop : Nat)
    (h : GoodMassWitness sample c minGoodWeight minDrop) :
    minDrop * minGoodWeight ≤ weightedDrop sample c :=
  good_mass_implies_weightedDrop_lower_bound sample c minGoodWeight minDrop h

def RuntimeSavingWitness (saving : Nat) : Prop := 0 < saving

theorem zero_is_not_runtime_saving : ¬ RuntimeSavingWitness 0 := by
  simp [RuntimeSavingWitness]

theorem c8_classical_endpoint_not_promoted : ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c7_classical_endpoint_not_promoted

theorem c8_k10_not_promoted : ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c7_k10_not_promoted

end CircuitC8
end MCore
