import MCore.CircuitC8

namespace MCore
namespace C9

open CircuitK1 CircuitC2 CircuitC3 CircuitC8

abbrev FormulaTree := Circuit

def D (ρ : Restriction) (t : FormulaTree) : FormulaTree :=
  restrictedSimplified ρ t

def mu (t : FormulaTree) : Nat := potential t

def delta (ρ : Restriction) (t : FormulaTree) : Nat :=
  mu t - mu (D ρ t)

@[simp] theorem D_eq (ρ : Restriction) (t : FormulaTree) :
    D ρ t = restrictedSimplified ρ t := rfl

@[simp] theorem mu_eq (t : FormulaTree) : mu t = potential t := rfl

@[simp] theorem delta_eq (ρ : Restriction) (t : FormulaTree) :
    delta ρ t = potential t - potential (restrictedSimplified ρ t) := rfl

end C9
end MCore
