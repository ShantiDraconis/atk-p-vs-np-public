import MCore.Real.CNFStructure
import MCore.Real.P01NeedExprTagDecode

namespace MCore
namespace Real
namespace P01CNFMode

open CircuitK1
open P01NeedExprTagDecode

/-- Finite syntactic obligation carried while traversing a prefix circuit.

No extra unbounded stack is required: continuation frames determine the mode
for each later right child. -/
inductive SyntaxMode where
  | cnf
  | clause
  | mustInput
  deriving DecidableEq, Repr

/-- Boolean semantics of a syntax mode, reusing the already-certified CNF and
clause recognizers. -/
def modeCheck : SyntaxMode → Circuit → Bool
  | .cnf, c => isCNFBool c
  | .clause, c => isClauseBool c
  | .mustInput, .input _ => true
  | .mustInput, _ => false

/-- Local tag admission rule implementable in finite control. -/
def tagAllowed : SyntaxMode → NeedExprTag → Bool
  | .cnf, .input => true
  | .cnf, .constFalse => true
  | .cnf, .constTrue => true
  | .cnf, .neg => true
  | .cnf, .and => true
  | .cnf, .or => true
  | .clause, .input => true
  | .clause, .constFalse => true
  | .clause, .neg => true
  | .clause, .or => true
  | .mustInput, .input => true
  | _, _ => false

/-- Expected mode for an immediate child of a valid operator tag. -/
def childMode : SyntaxMode → NeedExprTag → SyntaxMode
  | _, .neg => .mustInput
  | .cnf, .and => .cnf
  | _, .or => .clause
  | m, _ => m

@[simp] theorem modeCheck_cnf_eq (c : Circuit) :
    modeCheck .cnf c = isCNFBool c := rfl

@[simp] theorem modeCheck_clause_eq (c : Circuit) :
    modeCheck .clause c = isClauseBool c := rfl

theorem modeCheck_cnf_iff (c : Circuit) :
    modeCheck .cnf c = true ↔ IsCNF c := by
  exact isCNFBool_eq_true_iff c

theorem modeCheck_clause_iff (c : Circuit) :
    modeCheck .clause c = true ↔ IsClause c := by
  exact isClauseBool_eq_true_iff c

@[simp] theorem modeCheck_mustInput_iff (c : Circuit) :
    modeCheck .mustInput c = true ↔ ∃ i, c = .input i := by
  cases c with
  | input i =>
      simp [modeCheck]
  | const b =>
      simp [modeCheck]
  | not c =>
      simp [modeCheck]
  | and a b =>
      simp [modeCheck]
  | or a b =>
      simp [modeCheck]

/-- Input is admissible in all three modes. -/
@[simp] theorem modeCheck_input
    (mode : SyntaxMode) (i : Nat) :
    modeCheck mode (.input i) = tagAllowed mode .input := by
  cases mode <;> rfl

/-- False is both a clause and a CNF, but is not a demanded input literal. -/
@[simp] theorem modeCheck_constFalse
    (mode : SyntaxMode) :
    modeCheck mode (.const false) = tagAllowed mode .constFalse := by
  cases mode <;> rfl

/-- True is a CNF empty conjunction only. -/
@[simp] theorem modeCheck_constTrue
    (mode : SyntaxMode) :
    modeCheck mode (.const true) = tagAllowed mode .constTrue := by
  cases mode <;> rfl

/-- Root physical decoder tag of a semantic circuit. -/
def circuitTag : Circuit → NeedExprTag
  | .input _ => .input
  | .const false => .constFalse
  | .const true => .constTrue
  | .not _ => .neg
  | .and _ _ => .and
  | .or _ _ => .or

/-- Any circuit accepted by a syntax mode has a physically admissible root
tag in that same mode. -/
theorem tagAllowed_of_modeCheck
    (mode : SyntaxMode) (c : Circuit)
    (h : modeCheck mode c = true) :
    tagAllowed mode (circuitTag c) = true := by
  cases mode with
  | cnf =>
      cases c with
      | input i => rfl
      | const b => cases b <;> rfl
      | not c => rfl
      | and a b => rfl
      | or a b => rfl
  | clause =>
      cases c with
      | input i => rfl
      | const b =>
          cases b with
          | false => rfl
          | true =>
              simp [modeCheck, isClauseBool] at h
      | not c =>
          cases c with
          | input i => rfl
          | const b => simp [modeCheck, isClauseBool] at h
          | not c => simp [modeCheck, isClauseBool] at h
          | and a b => simp [modeCheck, isClauseBool] at h
          | or a b => simp [modeCheck, isClauseBool] at h
      | and a b =>
          simp [modeCheck, isClauseBool] at h
      | or a b =>
          rfl
  | mustInput =>
      cases c with
      | input i => rfl
      | const b => simp [modeCheck] at h
      | not c => simp [modeCheck] at h
      | and a b => simp [modeCheck] at h
      | or a b => simp [modeCheck] at h

/-- Negation is valid exactly when the current mode admits it and the child is
literally an input node. -/
theorem modeCheck_not
    (mode : SyntaxMode) (c : Circuit) :
    modeCheck mode (.not c) =
      (tagAllowed mode .neg &&
        modeCheck (childMode mode .neg) c) := by
  cases mode <;> cases c <;>
    simp [modeCheck, tagAllowed, childMode, isCNFBool, isClauseBool]

/-- Conjunction is admitted only in CNF mode, with both children in CNF mode. -/
theorem modeCheck_and
    (mode : SyntaxMode) (a b : Circuit) :
    modeCheck mode (.and a b) =
      (tagAllowed mode .and &&
        modeCheck .cnf a && modeCheck .cnf b) := by
  cases mode <;>
    simp [modeCheck, tagAllowed, isCNFBool, isClauseBool]

/-- Disjunction is admitted in CNF or clause mode, with both children required
to be clauses. -/
theorem modeCheck_or
    (mode : SyntaxMode) (a b : Circuit) :
    modeCheck mode (.or a b) =
      (tagAllowed mode .or &&
        modeCheck .clause a && modeCheck .clause b) := by
  cases mode <;>
    simp [modeCheck, tagAllowed, isCNFBool, isClauseBool]

#print axioms MCore.Real.P01CNFMode.tagAllowed_of_modeCheck
#print axioms MCore.Real.P01CNFMode.modeCheck_cnf_iff
#print axioms MCore.Real.P01CNFMode.modeCheck_clause_iff
#print axioms MCore.Real.P01CNFMode.modeCheck_mustInput_iff
#print axioms MCore.Real.P01CNFMode.modeCheck_not
#print axioms MCore.Real.P01CNFMode.modeCheck_and
#print axioms MCore.Real.P01CNFMode.modeCheck_or

end P01CNFMode
end Real
end MCore
