import MCore.Real.PNPDiscovery.FullSourceDichotomy

namespace MCore
namespace Real
namespace PNPDiscovery

/-- Four values of Option Bool cannot keep both parity classes pairwise
separated without a repetition inside one parity class. -/
theorem optionBool_four_cross_separated
    (a0 a1 a2 a3 : Option Bool)
    (h01 : a0 ≠ a1)
    (h03 : a0 ≠ a3)
    (h21 : a2 ≠ a1)
    (h23 : a2 ≠ a3) :
    a0 = a2 ∨ a1 = a3 := by
  cases a0 with
  | none =>
      cases a1 with
      | none => exact False.elim (h01 rfl)
      | some b1 =>
          cases b1 <;>
          cases a2 with
          | none => exact Or.inl rfl
          | some b2 =>
              cases b2 <;>
              cases a3 with
              | none => exact False.elim (h03 rfl)
              | some b3 =>
                  cases b3 <;> simp_all
  | some b0 =>
      cases b0 <;>
      cases a1 with
      | none =>
          cases a2 with
          | none => exact False.elim (h21 rfl)
          | some b2 =>
              cases b2 <;>
              cases a3 with
              | none => exact Or.inr rfl
              | some b3 =>
                  cases b3 <;> simp_all
      | some b1 =>
          cases b1 <;>
          cases a2 with
          | none =>
              cases a3 with
              | none => exact Or.inl rfl
              | some b3 =>
                  cases b3 <;> simp_all
          | some b2 =>
              cases b2 <;>
              cases a3 with
              | none => exact Or.inr rfl
              | some b3 =>
                  cases b3 <;> simp_all

/-- Pure finite head-barrier condition across four consecutive positive orbit
points: every cross-parity pair carries a different initial head symbol. -/
def FourPointHeadBarrier
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (n : Nat) : Prop :=
  let h0 := sourceHeadSymbol (orbit M hTotal seed (n + 1))
  let h1 := sourceHeadSymbol (orbit M hTotal seed (n + 2))
  let h2 := sourceHeadSymbol (orbit M hTotal seed (n + 3))
  let h3 := sourceHeadSymbol (orbit M hTotal seed (n + 4))
  h0 ≠ h1 ∧ h0 ≠ h3 ∧ h2 ≠ h1 ∧ h2 ≠ h3

/-- Therefore a pure head-only barrier necessarily repeats inside one parity
class after two steps. -/
theorem fourPointHeadBarrier_forces_sameParity_repeat
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (n : Nat)
    (H : FourPointHeadBarrier M hTotal seed n) :
    sourceHeadSymbol (orbit M hTotal seed (n + 1)) =
        sourceHeadSymbol (orbit M hTotal seed (n + 3)) ∨
      sourceHeadSymbol (orbit M hTotal seed (n + 2)) =
        sourceHeadSymbol (orbit M hTotal seed (n + 4)) := by
  dsimp [FourPointHeadBarrier] at H
  exact optionBool_four_cross_separated
    _ _ _ _
    H.1 H.2.1 H.2.2.1 H.2.2.2

/-- Hence HEAD cannot carry an injective unbounded counter; its only possible
barrier behavior is a finite parity partition with same-parity recurrence. -/
def HeadParityPartitionRegime
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString) : Prop :=
  ∀ n : Nat,
    sourceHeadSymbol (orbit M hTotal seed (n + 1)) =
        sourceHeadSymbol (orbit M hTotal seed (n + 3)) ∨
      sourceHeadSymbol (orbit M hTotal seed (n + 2)) =
        sourceHeadSymbol (orbit M hTotal seed (n + 4))

theorem fourPointHeadBarrier_all_to_partition
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (H : ∀ n : Nat, FourPointHeadBarrier M hTotal seed n) :
    HeadParityPartitionRegime M hTotal seed := by
  intro n
  exact fourPointHeadBarrier_forces_sameParity_repeat
    M hTotal seed n (H n)

#print axioms MCore.Real.PNPDiscovery.optionBool_four_cross_separated
#print axioms MCore.Real.PNPDiscovery.fourPointHeadBarrier_forces_sameParity_repeat
#print axioms MCore.Real.PNPDiscovery.fourPointHeadBarrier_all_to_partition

end PNPDiscovery
end Real
end MCore
