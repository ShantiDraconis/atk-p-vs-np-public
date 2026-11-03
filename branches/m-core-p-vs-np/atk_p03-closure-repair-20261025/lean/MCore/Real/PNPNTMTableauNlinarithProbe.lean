import Mathlib

namespace MCore.Real.PNPNTMTableauNlinarithProbe

theorem probe_linear_to_quadratic
    (a b r x : Nat)
    (hr : 1 ≤ r)
    (hx : x ≤ a + b * r) :
    x ≤ (a + b) * r ^ 2 := by
  nlinarith

theorem probe_bounded_product
    (a b c d x y r : Nat)
    (hr : 1 ≤ r)
    (hx : x ≤ a * r ^ 2)
    (hy : y ≤ b * r ^ 2)
    (hc : c ≤ a)
    (hd : d ≤ b) :
    13 * x * y + 3 ≤ (16 * a * b + 3) * r ^ 4 := by
  nlinarith

theorem probe_step_times_radius
    (t r q c l : Nat)
    (hr : 1 ≤ r)
    (ht : t ≤ r)
    (hlin : c + l * r ≤ (c + l) * r) :
    t * (3 * q * (c + l * r)) ≤
      (3 * q * (c + l)) * r ^ 2 := by
  nlinarith

theorem probe_sum_blocks
    (i tr f ci ct cf r : Nat)
    (hr : 1 ≤ r)
    (hi : i ≤ ci * r)
    (htr : tr ≤ ct * r ^ 2)
    (hf : f ≤ cf * r ^ 2) :
    i + tr + f ≤ (ci + ct + cf) * r ^ 2 := by
  nlinarith

end MCore.Real.PNPNTMTableauNlinarithProbe
