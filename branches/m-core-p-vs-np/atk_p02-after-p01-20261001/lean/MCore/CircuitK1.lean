import MCore.PrizeK0

namespace MCore
namespace CircuitK1

inductive Circuit where
  | input : Nat → Circuit
  | const : Bool → Circuit
  | not : Circuit → Circuit
  | and : Circuit → Circuit → Circuit
  | or : Circuit → Circuit → Circuit
  deriving DecidableEq, Repr

abbrev Restriction := Nat → Option Bool

def restrict (ρ : Restriction) : Circuit → Circuit
  | .input i => match ρ i with | some b => .const b | none => .input i
  | .const b => .const b
  | .not c => .not (restrict ρ c)
  | .and a b => .and (restrict ρ a) (restrict ρ b)
  | .or a b => .or (restrict ρ a) (restrict ρ b)

def size : Circuit → Nat
  | .input _ => 1
  | .const _ => 1
  | .not c => size c + 1
  | .and a b => size a + size b + 1
  | .or a b => size a + size b + 1

def depth : Circuit → Nat
  | .input _ => 0
  | .const _ => 0
  | .not c => depth c + 1
  | .and a b => max (depth a) (depth b) + 1
  | .or a b => max (depth a) (depth b) + 1

def μ (c : Circuit) : Nat := size c + depth c

@[simp] theorem restrict_const (ρ : Restriction) (b : Bool) : restrict ρ (.const b) = .const b := rfl
@[simp] theorem restrict_not (ρ : Restriction) (c : Circuit) : restrict ρ (.not c) = .not (restrict ρ c) := rfl
@[simp] theorem restrict_and (ρ : Restriction) (a b : Circuit) : restrict ρ (.and a b) = .and (restrict ρ a) (restrict ρ b) := rfl
@[simp] theorem restrict_or (ρ : Restriction) (a b : Circuit) : restrict ρ (.or a b) = .or (restrict ρ a) (restrict ρ b) := rfl

/-- Explicitly exposes both `Option Bool` branches; future structural proofs reuse
    this equation rather than assuming the simplifier performs the split. -/
theorem restrict_input_cases (ρ : Restriction) (i : Nat) :
    restrict ρ (.input i) = match ρ i with | some b => .const b | none => .input i := rfl

theorem size_restrict (ρ : Restriction) (c : Circuit) : size (restrict ρ c) = size c := by
  induction c with
  | input i => cases h : ρ i <;> simp [restrict_input_cases, h, size]
  | const b => rfl
  | not c ih => simp [restrict, size, ih]
  | and a b iha ihb => simp [restrict, size, iha, ihb]
  | or a b iha ihb => simp [restrict, size, iha, ihb]

theorem depth_restrict (ρ : Restriction) (c : Circuit) : depth (restrict ρ c) = depth c := by
  induction c with
  | input i => cases h : ρ i <;> simp [restrict_input_cases, h, depth]
  | const b => rfl
  | not c ih => simp [restrict, depth, ih]
  | and a b iha ihb => simp [restrict, depth, iha, ihb]
  | or a b iha ihb => simp [restrict, depth, iha, ihb]

theorem μ_restrict_invariant (ρ : Restriction) (c : Circuit) : μ (restrict ρ c) = μ c := by
  simp [μ, size_restrict, depth_restrict]

def fixesZeroTrue : Restriction
  | 0 => some true
  | _ => none

def leavesZeroFree : Restriction := fun _ => none

def oneInput : Circuit := .input 0

def twoInputOr : Circuit := .or (.input 0) (.input 1)

/-- Named adversarial regression: fixed input must take the `some` branch. -/
@[simp] theorem adversarial_input_some : restrict fixesZeroTrue oneInput = .const true := rfl

/-- Named adversarial regression: free input must take the `none` branch. -/
@[simp] theorem adversarial_input_none : restrict leavesZeroFree oneInput = oneInput := rfl

/-- Named adversarial regression for the previously damaged binary OR equation. -/
@[simp] theorem adversarial_restrict_or :
    restrict fixesZeroTrue twoInputOr = .or (.const true) (.input 1) := rfl

/-- Named regressions for both structural measures on the failing input pattern. -/
@[simp] theorem adversarial_size_restrict : size (restrict fixesZeroTrue oneInput) = size oneInput :=
  size_restrict fixesZeroTrue oneInput

@[simp] theorem adversarial_depth_restrict : depth (restrict fixesZeroTrue oneInput) = depth oneInput :=
  depth_restrict fixesZeroTrue oneInput

@[simp] theorem raw_potential_does_not_drop : μ (restrict fixesZeroTrue oneInput) = μ oneInput :=
  μ_restrict_invariant fixesZeroTrue oneInput

theorem k1_classical_endpoint_not_promoted : ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  prize_k0_classical_endpoint_not_promoted

theorem k1_k10_not_promoted : ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  prize_k0_k10_not_promoted

end CircuitK1
end MCore
