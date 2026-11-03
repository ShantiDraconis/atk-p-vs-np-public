import MCore.P012.P012Core

namespace MCore
namespace P012

inductive Formula where
  | const : Bool → Formula
  | var : Nat → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  deriving Repr, DecidableEq

def eval : Formula → List Bool → Bool
  | .const b, _ => b
  | .var n, w => w.getD n false
  | .not φ, w => !(eval φ w)
  | .and φ ψ, w => (eval φ w) && (eval ψ w)
  | .or φ ψ, w => (eval φ w) || (eval ψ w)

/-- P012's three tape symbols are represented concretely by Option Bool:
none=0, some false=1, some true=2. -/
def sigma012Code : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

def sigma012Decode : Nat → Option Bool
  | 0 => none
  | 1 => some false
  | 2 => some true
  | _ => none

theorem sigma012_code_none : sigma012Code none = 0 := rfl
theorem sigma012_code_false : sigma012Code (some false) = 1 := rfl
theorem sigma012_code_true : sigma012Code (some true) = 2 := rfl

theorem sigma012_decode_code (x : Option Bool) :
    sigma012Decode (sigma012Code x) = x := by
  cases x with
  | none => rfl
  | some b => cases b <;> rfl

/-- Logical reflexivity only: this theorem is intentionally not the repository's
physical verifier correctness theorem. -/
theorem L14_logical_reflexivity
    (φ : Formula) (w : List Bool) :
    eval φ w = eval φ w := rfl

def physicalAcceptSymbol : Option Bool → Bool
  | some true => true
  | _ => false

theorem blank_never_accepts :
    physicalAcceptSymbol none = false := rfl

theorem false_symbol_rejects :
    physicalAcceptSymbol (some false) = false := rfl

theorem true_symbol_accepts :
    physicalAcceptSymbol (some true) = true := rfl

end P012
end MCore
