import Mathlib
import MCore.Real.OpenMathCore.Arithmetic

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof

structure RealPotential where
  value : BitString → ℝ
  zero_value : value [] = 0

def massPotential : RealPotential where
  value := fun x => (arithmeticMass x : ℝ)
  zero_value := by simp [arithmeticMass, bitLength, bitWeight]

def addPotential (A B : RealPotential) : RealPotential where
  value := fun x => A.value x + B.value x
  zero_value := by simp [A.zero_value, B.zero_value]

def scalePotential (c : ℝ) (A : RealPotential) : RealPotential where
  value := fun x => c * A.value x
  zero_value := by simp [A.zero_value]

@[simp] theorem addPotential_apply (A B : RealPotential) (x : BitString) :
    (addPotential A B).value x = A.value x + B.value x := rfl

@[simp] theorem scalePotential_apply (c : ℝ) (A : RealPotential) (x : BitString) :
    (scalePotential c A).value x = c * A.value x := rfl

theorem addPotential_assoc (A B C : RealPotential) :
    ∀ x, (addPotential (addPotential A B) C).value x =
      (addPotential A (addPotential B C)).value x := by
  intro x
  simp [addPotential, add_assoc]

theorem scale_addPotential (c : ℝ) (A B : RealPotential) :
    ∀ x, (scalePotential c (addPotential A B)).value x =
      (addPotential (scalePotential c A) (scalePotential c B)).value x := by
  intro x
  simp [scalePotential, addPotential, mul_add]

end MCore.Real.OpenMathCore
