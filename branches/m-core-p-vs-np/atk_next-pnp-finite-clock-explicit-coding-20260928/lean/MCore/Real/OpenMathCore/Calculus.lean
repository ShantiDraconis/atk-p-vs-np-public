import Mathlib
import MCore.Real.OpenMathCore.Topology

namespace MCore.Real.OpenMathCore

open MeasureTheory

structure DifferentialBehavior where
  f : ℝ → ℝ
  df : ℝ → ℝ
  hasDeriv : ∀ x, HasDerivAt f (df x) x

structure IntegralBehavior where
  f : ℝ → ℝ
  integrable : ∀ a b : ℝ, IntervalIntegrable f volume a b

noncomputable def accumulated (I : IntegralBehavior) (a x : ℝ) : ℝ :=
  ∫ t in a..x, I.f t

def affineDifferential (m c : ℝ) : DifferentialBehavior where
  f := fun x => m * x + c
  df := fun _ => m
  hasDeriv := by
    intro x
    simpa using (hasDerivAt_id x).const_mul m |>.add_const c

def constantIntegral (c : ℝ) : IntegralBehavior where
  f := fun _ => c
  integrable := by
    intro a b
    exact intervalIntegrable_const

structure EnergyBehavior where
  potential : ℝ → ℝ
  nonnegative : ∀ x, 0 ≤ potential x
  derivative : ℝ → ℝ
  derivative_spec : ∀ x, HasDerivAt potential (derivative x) x

end MCore.Real.OpenMathCore
