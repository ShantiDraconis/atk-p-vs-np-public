import MCore.Real.P03TerminalSemanticBridge

namespace MCore
namespace Real
namespace P03CriticalHalfSymmetry

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TableauDynamics
open P03TerminalSemanticBridge

/-- Complement involution on the two parity-density coordinates. -/
def ComplementSymmetry (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - p.1, 1 - p.2)

/-- Reflection around the critical midpoint 1/2 on the real line. -/
def CriticalReflection (s : ℝ) : ℝ :=
  1 - s

/--
Affine map centered at 1/2.  It intertwines complementing both coordinates
with reflection around 1/2.
-/
def CriticalHalfMap (α : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) + α * (((p.1 + p.2) / 2) - (1 / 2 : ℝ))

@[simp] theorem complementSymmetry_involutive
    (p : ℝ × ℝ) :
    ComplementSymmetry (ComplementSymmetry p) = p := by
  rcases p with ⟨e, o⟩
  simp [ComplementSymmetry]

@[simp] theorem criticalReflection_involutive
    (s : ℝ) :
    CriticalReflection (CriticalReflection s) = s := by
  simp [CriticalReflection]

/-- Exact conjugacy law Φ ∘ C = R ∘ Φ. -/
theorem criticalHalfMap_intertwines
    (α : ℝ)
    (p : ℝ × ℝ) :
    CriticalHalfMap α (ComplementSymmetry p) =
      CriticalReflection (CriticalHalfMap α p) := by
  rcases p with ⟨e, o⟩
  simp [CriticalHalfMap, ComplementSymmetry, CriticalReflection]
  ring

/-- The balanced point is a fixed point of complement symmetry. -/
theorem balanced_pair_fixed :
    ComplementSymmetry ((1 / 2 : ℝ), (1 / 2 : ℝ)) =
      ((1 / 2 : ℝ), (1 / 2 : ℝ)) := by
  norm_num [ComplementSymmetry]

/-- Every affine critical-half map sends the balanced pair to 1/2. -/
theorem criticalHalfMap_balanced
    (α : ℝ) :
    CriticalHalfMap α ((1 / 2 : ℝ), (1 / 2 : ℝ)) =
      (1 / 2 : ℝ) := by
  ring_nf [CriticalHalfMap]

/-- The only real fixed point of s ↦ 1-s is 1/2. -/
theorem criticalReflection_fixed_iff
    (s : ℝ) :
    CriticalReflection s = s ↔ s = (1 / 2 : ℝ) := by
  unfold CriticalReflection
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    norm_num

/--
Pure symmetry package.  This is unconditional and contains no semantic claim
about any Turing-machine run.
-/
structure HalfSymmetryLaw where
  α : ℝ
  intertwines :
    ∀ p : ℝ × ℝ,
      CriticalHalfMap α (ComplementSymmetry p) =
        CriticalReflection (CriticalHalfMap α p)

def canonicalHalfSymmetry : HalfSymmetryLaw :=
  { α := 1
    intertwines := criticalHalfMap_intertwines 1 }

/--
The missing material preservation layer.  It does not merely map formal
coordinates: for every candidate it must actually produce an odd-separated
full-run acceptance witness.

This is deliberately the exact terminal mathematical burden, not an axiom or
an equivalent hypothesis hidden under a weaker name.
-/
structure HalfSymmetryMaterialBridge
    (S : HalfSymmetryLaw) where
  materialize :
    ∀ (M : PolyDTMCandidate)
      (hTotal : DeclaredClockTotal M),
      Nonempty (FullRunAcceptanceWitness M hTotal)

/-- Any genuine material bridge closes the exact terminal law. -/
theorem materialBridge_implies_fullRunAcceptanceLaw
    {S : HalfSymmetryLaw}
    (B : HalfSymmetryMaterialBridge S) :
    FullRunAcceptanceLaw := by
  intro M hTotal
  exact B.materialize M hTotal

/--
Conversely, the existing terminal law can populate the material field of any
pure half-symmetry package.  Thus the material bridge is not a new shortcut:
its mathematical content is exactly FullRunAcceptanceLaw.
-/
def materialBridge_of_fullRunAcceptanceLaw
    (S : HalfSymmetryLaw)
    (H : FullRunAcceptanceLaw) :
    HalfSymmetryMaterialBridge S :=
  { materialize := H }

theorem materialBridge_iff_fullRunAcceptanceLaw
    (S : HalfSymmetryLaw) :
    Nonempty (HalfSymmetryMaterialBridge S) ↔ FullRunAcceptanceLaw := by
  constructor
  · rintro ⟨B⟩
    exact materialBridge_implies_fullRunAcceptanceLaw B
  · intro H
    exact ⟨materialBridge_of_fullRunAcceptanceLaw S H⟩

/--
Pure 1/2 symmetry is structurally closed, while terminal closure still
requires the material bridge.
-/
theorem canonical_symmetry_is_closed :
    ∀ p : ℝ × ℝ,
      CriticalHalfMap canonicalHalfSymmetry.α (ComplementSymmetry p) =
        CriticalReflection (CriticalHalfMap canonicalHalfSymmetry.α p) :=
  canonicalHalfSymmetry.intertwines

#print axioms MCore.Real.P03CriticalHalfSymmetry.complementSymmetry_involutive
#print axioms MCore.Real.P03CriticalHalfSymmetry.criticalReflection_involutive
#print axioms MCore.Real.P03CriticalHalfSymmetry.criticalHalfMap_intertwines
#print axioms MCore.Real.P03CriticalHalfSymmetry.balanced_pair_fixed
#print axioms MCore.Real.P03CriticalHalfSymmetry.criticalHalfMap_balanced
#print axioms MCore.Real.P03CriticalHalfSymmetry.criticalReflection_fixed_iff
#print axioms MCore.Real.P03CriticalHalfSymmetry.canonical_symmetry_is_closed
#print axioms MCore.Real.P03CriticalHalfSymmetry.materialBridge_implies_fullRunAcceptanceLaw
#print axioms MCore.Real.P03CriticalHalfSymmetry.materialBridge_iff_fullRunAcceptanceLaw

end P03CriticalHalfSymmetry
end Real
end MCore
