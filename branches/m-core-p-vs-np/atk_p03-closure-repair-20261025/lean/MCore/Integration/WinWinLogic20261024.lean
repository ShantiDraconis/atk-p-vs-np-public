/-!
# Win-win (case split): exact logical content and its obstruction

The proposal "two complementary situations `A` and `¬ A` both exist and
together fix the result" has one consistent reading: the case split
`(A → X) → (¬ A → X) → X`.  Reading it as "`A` and `¬ A` hold together" is
inconsistent.

`missing_half_iff_target` is the obstruction found in every repository split:
when the opposite world lands inside the complementary branch, the missing
half of the win-win is equivalent to the target itself.

No imports: the file depends on the Lean core only.
-/

namespace MCore
namespace Integration
namespace WinWinLogic20261024

/-- The proposal, in its exact form: a case split. -/
theorem winwin_close {A X : Prop} (pos : A → X) (neg : ¬ A → X) : X := by
  cases Classical.em A with
  | inl h => exact pos h
  | inr h => exact neg h

/-- "Both sides hold at the same time" is not a consistent reading. -/
theorem simultaneous_sides_impossible {A : Prop} : ¬ (A ∧ ¬ A) :=
  fun h => h.2 h.1

/-- Generic obstruction: if the opposite world `Opp` lands inside the
complementary branch, the missing half is equivalent to the target.
Constructive. -/
theorem missing_half_iff_target {Opp Branch Target : Prop}
    (hOpp : Opp → Branch) (hTarget : Target ↔ ¬ Opp) :
    (Branch → Target) ↔ Target := by
  constructor
  · intro half
    exact hTarget.mpr (fun o => (hTarget.mp (half (hOpp o))) o)
  · intro t _
    exact t

/-- With the target itself as the split (`X := RH`), the negative half
`¬ RH → RH` is equivalent to `RH`. -/
theorem self_target_missing_half {RH : Prop} :
    (¬ RH → RH) ↔ RH :=
  missing_half_iff_target (Opp := ¬ RH) (Branch := ¬ RH) id
    ⟨fun h n => n h, fun h => Classical.byContradiction h⟩

end WinWinLogic20261024
end Integration
end MCore

#print axioms MCore.Integration.WinWinLogic20261024.winwin_close
#print axioms MCore.Integration.WinWinLogic20261024.simultaneous_sides_impossible
#print axioms MCore.Integration.WinWinLogic20261024.missing_half_iff_target
#print axioms MCore.Integration.WinWinLogic20261024.self_target_missing_half
