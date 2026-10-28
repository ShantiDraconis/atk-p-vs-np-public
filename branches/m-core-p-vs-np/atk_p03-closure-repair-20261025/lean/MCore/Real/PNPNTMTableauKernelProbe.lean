import Mathlib

namespace MCore.Real.PNPNTMTableauKernelProbe

theorem probe_mem_ofFn
    {n : Nat} (f : Fin n → Nat) (x : Nat)
    (hx : x ∈ List.ofFn f) :
    ∃ i : Fin n, f i = x := by
  rw [List.mem_ofFn] at hx
  exact hx

theorem probe_mem_flatten
    {α : Type} (xss : List (List α)) (x : α)
    (hx : x ∈ xss.flatten) :
    ∃ xs ∈ xss, x ∈ xs := by
  rw [List.mem_flatten] at hx
  exact hx

theorem probe_mem_flatMap
    {α β : Type} (xs : List α) (f : α → List β) (y : β)
    (hy : y ∈ xs.flatMap f) :
    ∃ x ∈ xs, y ∈ f x := by
  rw [List.mem_flatMap] at hy
  exact hy

theorem probe_add_div_of_lt_right
    (a b stride : Nat)
    (hstride : 0 < stride)
    (hb : b < stride) :
    (a * stride + b) / stride = a := by
  rw [Nat.add_div_of_lt_right hb]
  simp [hstride]

end MCore.Real.PNPNTMTableauKernelProbe
