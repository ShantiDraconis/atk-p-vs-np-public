import Mathlib

/-!
# ATK — Beal: enunciado preso aos naturais e descida com medida bem fundada

Corrige o `BealDescentClosure` do m-core-beal, cuja medida não exigia boa fundação
(ver `ATK.LogicAudit.beal_descent_without_wellfoundedness`).

* `BealStatement` — Aˣ + Bʸ = Cᶻ com A, B, C > 0 e x, y, z > 2 ⇒ gcd(A, B, C) > 1.
* `WFDescent` — medida em ℕ (bem fundada) que decresce estritamente sob uma transformação
  de soluções primitivas (gcd = 1).
* `beal_of_descent` — uma tal descida prova Beal.
* `descent_of_beal` — e Beal fornece uma tal descida (sobre o tipo vazio).
Logo, achar a descida é EXATAMENTE provar Beal: o item da agenda não é mais fácil que a conjectura.
-/

namespace ATK.BealDescent

def BealStatement : Prop :=
  ∀ A B C x y z : ℕ, 0 < A → 0 < B → 0 < C → 2 < x → 2 < y → 2 < z →
    A ^ x + B ^ y = C ^ z → 1 < Nat.gcd A (Nat.gcd B C)

structure PrimitiveSolution where
  A : ℕ
  B : ℕ
  C : ℕ
  x : ℕ
  y : ℕ
  z : ℕ
  hA : 0 < A
  hB : 0 < B
  hC : 0 < C
  hx : 2 < x
  hy : 2 < y
  hz : 2 < z
  equation : A ^ x + B ^ y = C ^ z
  coprime : Nat.gcd A (Nat.gcd B C) = 1

structure WFDescent where
  measure : PrimitiveSolution → ℕ
  transform : PrimitiveSolution → PrimitiveSolution
  strictDecrease : ∀ s, measure (transform s) < measure s

theorem no_primitive_of_descent (d : WFDescent) (s : PrimitiveSolution) : False := by
  have key : ∀ n, ∀ s : PrimitiveSolution, d.measure s = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs
      have hlt : d.measure (d.transform s) < n := by
        rw [← hs]
        exact d.strictDecrease s
      exact ih _ hlt (d.transform s) rfl
  exact key _ s rfl

theorem beal_of_descent (d : WFDescent) : BealStatement := by
  intro A B C x y z hA hB hC hx hy hz heq
  by_contra hle
  push_neg at hle
  have hpos : 0 < Nat.gcd A (Nat.gcd B C) := Nat.gcd_pos_of_pos_left _ hA
  have h1 : Nat.gcd A (Nat.gcd B C) = 1 := by omega
  exact no_primitive_of_descent d ⟨A, B, C, x, y, z, hA, hB, hC, hx, hy, hz, heq, h1⟩

theorem descent_of_beal (h : BealStatement) : Nonempty WFDescent :=
  ⟨{ measure := fun _ => 0,
     transform := id,
     strictDecrease := fun s => by
       have := h s.A s.B s.C s.x s.y s.z s.hA s.hB s.hC s.hx s.hy s.hz s.equation
       rw [s.coprime] at this
       omega }⟩

theorem descent_iff_beal : Nonempty WFDescent ↔ BealStatement :=
  ⟨fun ⟨d⟩ => beal_of_descent d, descent_of_beal⟩

end ATK.BealDescent

#print axioms ATK.BealDescent.no_primitive_of_descent
#print axioms ATK.BealDescent.beal_of_descent
#print axioms ATK.BealDescent.descent_of_beal
#print axioms ATK.BealDescent.descent_iff_beal
