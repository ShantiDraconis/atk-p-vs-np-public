import MCore.Real.Model
import Init.Data.Nat.Div.Lemmas

namespace MCore
namespace Real
namespace P01FiniteCodec

/-- Explicit finite encoding with a decoder that is a left inverse.
This is deliberately independent of Mathlib/Fintype. -/
structure FinCodec (α : Type) where
  size : Nat
  pos : 0 < size
  encode : α → Fin size
  decode : Fin size → α
  decode_encode : ∀ x, decode (encode x) = x

def unitCodec : FinCodec Unit where
  size := 1
  pos := by decide
  encode := fun _ => ⟨0, by decide⟩
  decode := fun _ => ()
  decode_encode := by intro x; cases x; rfl

def boolCodec : FinCodec Bool where
  size := 2
  pos := by decide
  encode
    | false => ⟨0, by decide⟩
    | true => ⟨1, by decide⟩
  decode := fun i => i.val = 1
  decode_encode := by
    intro b
    cases b <;> rfl

/-- Identity codec for a nonempty Fin type. -/
def finCodec (n : Nat) (h : 0 < n) : FinCodec (Fin n) where
  size := n
  pos := h
  encode := id
  decode := id
  decode_encode := by intro x; rfl

/-- Transport a codec along an explicit retraction. -/
def mapCodec {α β : Type}
    (C : FinCodec β)
    (toRep : α → β)
    (fromRep : β → α)
    (h : ∀ x, fromRep (toRep x) = x) :
    FinCodec α where
  size := C.size
  pos := C.pos
  encode := fun x => C.encode (toRep x)
  decode := fun i => fromRep (C.decode i)
  decode_encode := by
    intro x
    simp [C.decode_encode, h]

/-- Disjoint-block codec for sums. -/
def sumCodec {α β : Type}
    (A : FinCodec α) (B : FinCodec β) :
    FinCodec (Sum α β) where
  size := A.size + B.size
  pos := Nat.add_pos_left A.pos B.size
  encode
    | .inl a =>
        ⟨(A.encode a).val, Nat.lt_of_lt_of_le (A.encode a).isLt (Nat.le_add_right _ _)⟩
    | .inr b =>
        ⟨A.size + (B.encode b).val, by omega⟩
  decode := fun k =>
    if h : k.val < A.size then
      .inl (A.decode ⟨k.val, h⟩)
    else
      .inr (B.decode ⟨k.val - A.size, by omega⟩)
  decode_encode := by
    intro x
    cases x with
    | inl a =>
        simp [A.decode_encode, A.encode a |>.isLt]
    | inr b =>
        have h : ¬ (A.size + (B.encode b).val < A.size) := by omega
        simp [h, B.decode_encode]

/-- Row-major product codec. -/
def prodCodec {α β : Type}
    (A : FinCodec α) (B : FinCodec β) :
    FinCodec (α × β) where
  size := A.size * B.size
  pos := Nat.mul_pos A.pos B.pos
  encode := fun x =>
    ⟨(A.encode x.1).val * B.size + (B.encode x.2).val, by
      have ha := (A.encode x.1).isLt
      have hb := (B.encode x.2).isLt
      nlinarith⟩
  decode := fun k =>
    let qa : Fin A.size :=
      ⟨k.val / B.size, by
        exact (Nat.div_lt_iff_lt_mul B.pos).2 (by
          simpa [Nat.mul_comm] using k.isLt)⟩
    let qb : Fin B.size :=
      ⟨k.val % B.size, Nat.mod_lt _ B.pos⟩
    (A.decode qa, B.decode qb)
  decode_encode := by
    intro x
    rcases x with ⟨a,b⟩
    apply Prod.ext
    · simp [prodCodec, Nat.mul_add_div, Nat.div_eq_of_lt (B.encode b).isLt,
        A.decode_encode]
    · simp [prodCodec, Nat.mul_add_mod_self_left,
        Nat.mod_eq_of_lt (B.encode b).isLt, B.decode_encode]

/-- Nested three-way sum helper. -/
def sum3Codec {α β γ : Type}
    (A : FinCodec α) (B : FinCodec β) (C : FinCodec γ) :
    FinCodec (Sum α (Sum β γ)) :=
  sumCodec A (sumCodec B C)

/-- Nested four-way sum helper. -/
def sum4Codec {α β γ δ : Type}
    (A : FinCodec α) (B : FinCodec β) (C : FinCodec γ) (D : FinCodec δ) :
    FinCodec (Sum α (Sum β (Sum γ δ))) :=
  sumCodec A (sumCodec B (sumCodec C D))

#eval boolCodec.size

#print axioms MCore.Real.P01FiniteCodec.sumCodec
#print axioms MCore.Real.P01FiniteCodec.prodCodec

end P01FiniteCodec
end Real
end MCore
