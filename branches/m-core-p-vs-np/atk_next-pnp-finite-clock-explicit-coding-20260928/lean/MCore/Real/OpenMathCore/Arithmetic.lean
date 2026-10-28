import Mathlib
import MCore.Real.P02UniversalFailureAlgebra

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof

def bitNat : Bool → Nat
  | false => 0
  | true => 1

def bitWeight : BitString → Nat
  | [] => 0
  | b :: xs => bitNat b + bitWeight xs

def bitLength (x : BitString) : Nat := x.length

def arithmeticMass (x : BitString) : Nat :=
  bitLength x + bitWeight x

@[simp] theorem bitWeight_nil : bitWeight ([] : BitString) = 0 := rfl

@[simp] theorem bitWeight_cons (b : Bool) (xs : BitString) :
    bitWeight (b :: xs) = bitNat b + bitWeight xs := rfl

@[simp] theorem bitWeight_append (x y : BitString) :
    bitWeight (x ++ y) = bitWeight x + bitWeight y := by
  induction x with
  | nil => simp
  | cons b xs ih =>
      simp [bitWeight, ih, Nat.add_assoc]

@[simp] theorem bitLength_nil : bitLength ([] : BitString) = 0 := rfl

@[simp] theorem bitLength_append (x y : BitString) :
    bitLength (x ++ y) = bitLength x + bitLength y := by
  simp [bitLength]

theorem bitNat_le_one (b : Bool) : bitNat b ≤ 1 := by
  cases b <;> simp [bitNat]

theorem bitWeight_le_length (x : BitString) :
    bitWeight x ≤ bitLength x := by
  induction x with
  | nil => simp [bitWeight, bitLength]
  | cons b xs ih =>
      have ih' : bitWeight xs ≤ xs.length := by
        simpa [bitLength] using ih
      have hb : bitNat b ≤ 1 := bitNat_le_one b
      have hsum : bitNat b + bitWeight xs ≤ 1 + xs.length :=
        Nat.add_le_add hb ih'
      simpa [bitWeight, bitLength, Nat.add_comm] using hsum

theorem arithmeticMass_append (x y : BitString) :
    arithmeticMass (x ++ y) = arithmeticMass x + arithmeticMass y := by
  simp [arithmeticMass, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

structure ArithmeticLaw where
  measure : BitString → Nat
  nonnegative : ∀ x, 0 ≤ measure x
  append_bound :
    ∀ x y, measure (x ++ y) ≤
      measure x + measure y + (x.length + y.length)

def arithmeticMassLaw : ArithmeticLaw where
  measure := arithmeticMass
  nonnegative := by intro x; exact Nat.zero_le _
  append_bound := by
    intro x y
    rw [arithmeticMass_append]
    exact Nat.le_add_right _ _

end MCore.Real.OpenMathCore
