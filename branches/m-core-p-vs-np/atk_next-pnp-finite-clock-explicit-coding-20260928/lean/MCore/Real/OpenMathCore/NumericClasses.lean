import Mathlib
import MCore.Real.OpenMathCore.Algebra

namespace MCore.Real.OpenMathCore

class NumericObservable (α : Type) where
  toReal : α → ℝ
  norm : α → ℝ
  norm_nonneg : ∀ a, 0 ≤ norm a

instance : NumericObservable Nat where
  toReal := fun n => n
  norm := fun n => n
  norm_nonneg := by intro n; positivity

instance : NumericObservable Int where
  toReal := fun z => z
  norm := fun z => |(z : ℝ)|
  norm_nonneg := by intro z; exact abs_nonneg _

instance : NumericObservable Rat where
  toReal := fun q => q
  norm := fun q => |(q : ℝ)|
  norm_nonneg := by intro q; exact abs_nonneg _

instance : NumericObservable Real where
  toReal := id
  norm := abs
  norm_nonneg := abs_nonneg

def liftObservable {α : Type} [NumericObservable α] (f : BitString → α) :
    BitString → ℝ :=
  fun x => NumericObservable.toReal (f x)

def observableNorm {α : Type} [NumericObservable α] (a : α) : ℝ :=
  NumericObservable.norm a

theorem observableNorm_nonneg {α : Type} [NumericObservable α] (a : α) :
    0 ≤ observableNorm a :=
  NumericObservable.norm_nonneg a

end MCore.Real.OpenMathCore
