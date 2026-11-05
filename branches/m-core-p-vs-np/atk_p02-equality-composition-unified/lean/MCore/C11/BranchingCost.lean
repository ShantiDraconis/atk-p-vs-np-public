import MCore.C10.RestrictionProgress

namespace MCore
namespace C11

open C9 C10 CircuitC8 CircuitK1 CircuitC2 CircuitC3

/-- Syntactic variables of `t` that are assigned by `ρ`.
Duplicates are removed only when counting. -/
def fixedVarList (ρ : Restriction) : FormulaTree → List Nat
  | .input i =>
      match ρ i with
      | some _ => [i]
      | none => []
  | .const _ => []
  | .not c => fixedVarList ρ c
  | .and a b => fixedVarList ρ a ++ fixedVarList ρ b
  | .or a b => fixedVarList ρ a ++ fixedVarList ρ b

/-- Number of distinct syntactic variables of `t` fixed by `ρ`. -/
def fixedVarsCount (ρ : Restriction) (t : FormulaTree) : Nat :=
  (fixedVarList ρ t).eraseDups.length

/-- Exact bit-cost proxy for enumerating every Boolean assignment to the
variables fixed by a branch restriction. -/
def costBits (ρ : Restriction) (t : FormulaTree) : Nat :=
  fixedVarsCount ρ t

/-- Enumeration cost associated with `costBits`: exactly `2^k` branches. -/
def BranchingCost (ρ : Restriction) (t : FormulaTree) : Nat :=
  2 ^ costBits ρ t

theorem branchingCost_exact (ρ : Restriction) (t : FormulaTree) :
    BranchingCost ρ t = 2 ^ costBits ρ t := rfl

/-- Explicit weighted structural potential. The weights are data, not hidden
constants, and no classical-complexity interpretation is attached here. -/
def Potential (α β : Nat) (t : FormulaTree) : Nat :=
  α * vars t + β * stateRank t

/-- One-step quantitative payoff test using the exact exponent `costBits`
instead of an approximate logarithm. -/
def PaysOff (α β : Nat) (ρ : Restriction) (t : FormulaTree) : Prop :=
  Potential α β (D ρ t) + costBits ρ t < Potential α β t

/-- Raw deterministic measurements used by the C11 regression executable. -/
structure Metrics where
  varsBefore : Nat
  varsAfter : Nat
  deltaVars : Nat
  muBefore : Nat
  muAfter : Nat
  deltaMu : Nat
  rankBefore : Nat
  rankAfter : Nat
  deltaRank : Nat
  costBits : Nat
  branchingCost : Nat
  potentialBefore : Nat
  potentialAfter : Nat
  payoffLhs : Nat
  deriving Repr, DecidableEq

def metrics (α β : Nat) (ρ : Restriction) (t : FormulaTree) : Metrics :=
  let vt := vars t
  let vd := vars (D ρ t)
  let mt := mu t
  let md := mu (D ρ t)
  let rt := stateRank t
  let rd := stateRank (D ρ t)
  let cb := costBits ρ t
  let pb := Potential α β t
  let pa := Potential α β (D ρ t)
  { varsBefore := vt
    varsAfter := vd
    deltaVars := vt - vd
    muBefore := mt
    muAfter := md
    deltaMu := mt - md
    rankBefore := rt
    rankAfter := rd
    deltaRank := rt - rd
    costBits := cb
    branchingCost := BranchingCost ρ t
    potentialBefore := pb
    potentialAfter := pa
    payoffLhs := pa + cb }

/-- C11 does not assert payoff universally. It merely records the exact
quantitative proposition to be tested/proved on restricted families. -/
def UniversalPayoffObligation (α β : Nat) : Prop :=
  ∀ (ρ : Restriction) (t : FormulaTree),
    RestrictionProgress ρ t → PaysOff α β ρ t

/-- Stronger asymptotic/runtime interpretations are intentionally absent.
The inherited classical endpoint remains fail-closed. -/
theorem c11_classical_endpoint_not_promoted :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c10_classical_endpoint_not_promoted

theorem c11_k10_not_promoted :
    ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c10_k10_not_promoted

end C11
end MCore
