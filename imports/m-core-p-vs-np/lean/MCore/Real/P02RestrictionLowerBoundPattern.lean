import MCore.C11.BranchingCost
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P02RestrictionLowerBoundPattern

open C9 C10 C11 CircuitK1

/-- Exact amortized structural drop used by C11. -/
def amortizedDrop (α β : Nat) (ρ : Restriction) (t : FormulaTree) : Nat :=
  Potential α β t - Potential α β (D ρ t)

/-- C11 PaysOff is exactly the regime where the number of fixed branching bits
is strictly smaller than the certified potential drop. -/
theorem paysOff_implies_costBits_lt_amortizedDrop
    (α β : Nat) (ρ : Restriction) (t : FormulaTree)
    (h : PaysOff α β ρ t) :
    costBits ρ t < amortizedDrop α β ρ t := by
  unfold PaysOff amortizedDrop at *
  omega

/-- Separation-oriented local pattern: every progressing restriction fails to
amortize its branching bits. This is intentionally the opposite orientation
from C11 PaysOff. -/
def PersistentBranchingDeficit
    (α β : Nat) (t : FormulaTree) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgress ρ t →
      amortizedDrop α β ρ t ≤ costBits ρ t

theorem persistentBranchingDeficit_excludes_payoff
    (α β : Nat) (t : FormulaTree)
    (h : PersistentBranchingDeficit α β t) :
    ∀ ρ : Restriction,
      RestrictionProgress ρ t →
        ¬ PaysOff α β ρ t := by
  intro ρ hprog hpay
  have hlt := paysOff_implies_costBits_lt_amortizedDrop α β ρ t hpay
  have hle := h ρ hprog
  omega

/-- Family-level candidate obstruction for the fourth P02 lane.  Unlike the
old diagonal lanes, this statement contains no self-code or fixed-point
equation. -/
def PersistentBranchingDeficitFamily
    (α β : Nat) (f : Nat → FormulaTree) : Prop :=
  ∀ n : Nat, 0 < n → PersistentBranchingDeficit α β (f n)

/-- The canonical SAT bit language used by the P02 lanes. -/
abbrev CanonicalSAT : CanonicalFinalProof.BitLanguage :=
  CanonicalSATBoundary.SATBits CanonicalCircuitBits.circuitBitEncoding

/-- A formula family computes a bit language when, on every input `x`, the
formula for length `|x|` reads bit `i` of `x` as variable `i`. -/
def ComputesBitLanguage
    (L : CanonicalFinalProof.BitLanguage) (f : Nat → FormulaTree) : Prop :=
  ∀ x : CanonicalFinalProof.BitString,
    (CircuitC2.eval (fun i => x.getD i false) (f x.length) = true ↔ L x)

/-- Polynomially bounded formula size. -/
def PolynomialFormulaSize (f : Nat → FormulaTree) : Prop :=
  ∃ c k : Nat, ∀ n : Nat, size (f n) ≤ c * (n + 1) ^ k

/-- Exact open frontier for this pattern.

Historical version (conclusion `True`, so it carried no content):

    ∀ f, PersistentBranchingDeficitFamily 1 1 f → True

The statement below keeps the deficit hypothesis explicit and asks for a
concrete complexity conclusion in the model these trees actually live in.
`FormulaTree` has no gate sharing, so the reachable conclusion is a
*formula*-size lower bound.  That would give NP ⊄ non-uniform NC¹; it does not
by itself give SAT ∉ P, since P ⊆ NC¹ is not known to fail.

Status: OPEN.  It is neither proved nor assumed anywhere, and it may be false
(a polynomial-size SAT formula family with a persistent deficit would refute
it). -/
def RestrictionLowerBoundTransfer : Prop :=
  ∀ f : Nat → FormulaTree,
    ComputesBitLanguage CanonicalSAT f →
    PersistentBranchingDeficitFamily 1 1 f →
      ¬ PolynomialFormulaSize f

/-- Wiring only: the transfer, together with a persistent deficit for every
SAT-computing formula family, rules out polynomial-size SAT formulas.  Both
inputs are open; nothing here inhabits them. -/
theorem transfer_gives_formula_lower_bound
    (hT : RestrictionLowerBoundTransfer)
    (hD : ∀ f : Nat → FormulaTree,
      ComputesBitLanguage CanonicalSAT f →
        PersistentBranchingDeficitFamily 1 1 f) :
    ∀ f : Nat → FormulaTree,
      ComputesBitLanguage CanonicalSAT f → ¬ PolynomialFormulaSize f :=
  fun f hf => hT f hf (hD f hf)

#print axioms MCore.Real.P02RestrictionLowerBoundPattern.paysOff_implies_costBits_lt_amortizedDrop
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.persistentBranchingDeficit_excludes_payoff
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.transfer_gives_formula_lower_bound

end P02RestrictionLowerBoundPattern
end Real
end MCore
