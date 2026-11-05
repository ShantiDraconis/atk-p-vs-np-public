import MCore.C9.Progress

namespace MCore
namespace C9

/-- The finite restriction cube on exactly n active coordinates. -/
abbrev FiniteRestriction (n : Nat) := Fin n → Option Bool

instance (n : Nat) : Fintype (FiniteRestriction n) := Pi.fintype

theorem finiteRestriction_card (n : Nat) :
    Fintype.card (FiniteRestriction n) = 3 ^ n := by
  simp [FiniteRestriction, Fintype.card_option]

/-- The unique restriction fixing no active coordinate. -/
def allNone (n : Nat) : FiniteRestriction n := fun _ => none

def FiniteGood {n : Nat} (ρ : FiniteRestriction n) : Prop :=
  ∃ i : Fin n, ρ i ≠ none

instance finiteGoodDecidable {n : Nat} (ρ : FiniteRestriction n) :
    Decidable (FiniteGood ρ) := inferInstance

theorem not_finiteGood_iff {n : Nat} (ρ : FiniteRestriction n) :
    ¬ FiniteGood ρ ↔ ρ = allNone n := by
  constructor
  · intro h
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  · intro h hg
    obtain ⟨i, hi⟩ := hg
    subst ρ
    exact hi rfl

def goodFinset (n : Nat) : Finset (FiniteRestriction n) :=
  Finset.univ.filter FiniteGood

theorem allNone_not_good (n : Nat) : ¬ FiniteGood (allNone n) := by
  rw [not_finiteGood_iff]

theorem goodFinset_compl_eq_singleton (n : Nat) :
    (goodFinset n)ᶜ = {allNone n} := by
  ext ρ
  simp [goodFinset, not_finiteGood_iff]

theorem finiteGood_card (n : Nat) :
    (goodFinset n).card = 3 ^ n - 1 := by
  have htotal : (Finset.univ : Finset (FiniteRestriction n)).card = 3 ^ n := by
    simp [finiteRestriction_card]
  have hsplit :
      (goodFinset n).card + ((goodFinset n)ᶜ).card =
        (Finset.univ : Finset (FiniteRestriction n)).card := by
    simpa using Finset.card_add_card_compl (goodFinset n)
  rw [goodFinset_compl_eq_singleton] at hsplit
  simp at hsplit
  omega

/-- Exact rational mass; n=0 is handled without division-by-zero because 3^0=1. -/
def goodMass (n : Nat) : Rat :=
  ((3 ^ n - 1 : Nat) : Rat) / ((3 ^ n : Nat) : Rat)

theorem goodMass_zero : goodMass 0 = 0 := by native_decide
theorem goodMass_one : goodMass 1 = 2 / 3 := by native_decide
theorem goodMass_two : goodMass 2 = 8 / 9 := by native_decide
theorem goodMass_three : goodMass 3 = 26 / 27 := by native_decide
theorem goodMass_four : goodMass 4 = 80 / 81 := by native_decide

end C9
end MCore
