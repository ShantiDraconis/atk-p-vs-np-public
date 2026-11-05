import Mathlib
import MCore.Real.OpenMathCore.T5FBridge
import MCore.Real.P02ClockedDiagonalCompiler
import MCore.Real.P02DiagonalCompilerFrontierV2

namespace MCore
namespace Real
namespace OpenMathUniversalSeparationLaw

open Set Filter
open scoped Topology
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02UniversalFailureAlgebra
open P02ClockedDiagonalCompiler
open P02DiagonalCompilerFrontierV2
open OpenMathCore

/-- Closed begin/mid/end geometry. -/
def closedBegin : Set ℝ := {0}
def closedEnd : Set ℝ := {1}
def closedMid (mid : ℝ) : Set ℝ := {mid}
def closedInterval : Set ℝ := Set.Icc 0 1

theorem closedBegin_isClosed : IsClosed closedBegin := by
  simpa [closedBegin] using (isClosed_singleton : IsClosed ({0} : Set ℝ))

theorem closedMid_isClosed (mid : ℝ) : IsClosed (closedMid mid) := by
  simpa [closedMid] using (isClosed_singleton : IsClosed ({mid} : Set ℝ))

theorem closedEnd_isClosed : IsClosed closedEnd := by
  simpa [closedEnd] using (isClosed_singleton : IsClosed ({1} : Set ℝ))

theorem closedInterval_isClosed : IsClosed closedInterval := by
  exact isClosed_Icc

/-- Contraction around one distinguished fixed midpoint.  The midpoint must be
a field of the structure; requiring F m = m for every m would force F = id. -/
structure Contraction (F : ℝ → ℝ) (mid q : ℝ) where
  q_nonneg : 0 ≤ q
  q_lt_one : q < 1
  lipschitz : ∀ a b, |F a - F b| ≤ q * |a - b|
  maps_interval : ∀ x ∈ Set.Icc (0 : ℝ) 1, F x ∈ Set.Icc (0 : ℝ) 1
  fixes_mid : F mid = mid

structure RepelAndPull (F : ℝ → ℝ) (mid : ℝ) where
  pulls_begin : F 0 > 0
  pulls_end : F 1 < 1
  repels_mid : ∀ x, x ≠ mid → |F x - mid| > 0
  pull_to_mid : ∀ x ∈ Set.Icc (0 : ℝ) 1, |F x - mid| ≤ |x - mid|
  strict_contraction_outside :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ mid → |F x - mid| < |x - mid|

noncomputable def midpoint : ℝ := 1 / 2

noncomputable def midpointMap (x : ℝ) : ℝ := (x + midpoint) / 2

theorem midpointMap_sub_midpoint (x : ℝ) :
    midpointMap x - midpoint = (x - midpoint) / 2 := by
  unfold midpointMap midpoint
  ring

theorem midpointMap_contraction :
    Contraction midpointMap midpoint (1 / 2) := by
  refine
    { q_nonneg := by norm_num
      q_lt_one := by norm_num
      lipschitz := ?_
      maps_interval := ?_
      fixes_mid := ?_ }
  · intro a b
    calc
      |midpointMap a - midpointMap b|
          = |(a - b) / 2| := by
              congr 1
              unfold midpointMap midpoint
              ring
      _ = |a - b| / 2 := by
            rw [abs_div]
            norm_num
      _ = (1 / 2 : ℝ) * |a - b| := by ring
      _ ≤ (1 / 2 : ℝ) * |a - b| := le_rfl
  · intro x hx
    rcases hx with ⟨hx0, hx1⟩
    constructor
    · unfold midpointMap midpoint
      linarith
    · unfold midpointMap midpoint
      linarith
  · norm_num [midpointMap, midpoint]

theorem midpointMap_repelPull :
    RepelAndPull midpointMap midpoint := by
  refine
    { pulls_begin := ?_
      pulls_end := ?_
      repels_mid := ?_
      pull_to_mid := ?_
      strict_contraction_outside := ?_ }
  · norm_num [midpointMap, midpoint]
  · norm_num [midpointMap, midpoint]
  · intro x hx
    rw [midpointMap_sub_midpoint]
    exact abs_pos.mpr (div_ne_zero (sub_ne_zero.mpr hx) (by norm_num))
  · intro x _
    rw [midpointMap_sub_midpoint]
    rw [abs_div]
    norm_num
  · intro x _ hx
    rw [midpointMap_sub_midpoint, abs_div]
    have hpos : 0 < |x - midpoint| := abs_pos.mpr (sub_ne_zero.mpr hx)
    norm_num
    simpa using (half_lt_self hpos)

structure RatioTendsToOne (x y : ℕ → ℝ) : Prop where
  ratio_tends_one : Tendsto (fun n => y n / x n) atTop (𝓝 1)

def ratioX (n : ℕ) : ℝ := (n : ℝ) + 1
def ratioY (n : ℕ) : ℝ := ratioX n

def ratioLaw : RatioTendsToOne ratioX ratioY where
  ratio_tends_one := by
    have hEq : (fun n : ℕ => ratioY n / ratioX n) = fun _ => (1 : ℝ) := by
      funext n
      have hne : (n : ℝ) + 1 ≠ 0 := by positivity
      simp [ratioX, ratioY, hne]
    rw [hEq]
    exact tendsto_const_nhds

/-- Geometry and asymptotics are concrete. The terminal computational
separation remains an explicit proof field. -/
structure UniversalSeparationLaw where
  mid : ℝ
  mid_mem : mid ∈ Set.Icc (0 : ℝ) 1
  F : ℝ → ℝ
  q : ℝ
  contraction : Contraction F mid q
  repelPull : RepelAndPull F mid
  begin_closed : IsClosed closedBegin
  mid_closed : IsClosed (closedMid mid)
  end_closed : IsClosed closedEnd
  interval_closed : IsClosed closedInterval
  ratio : RatioTendsToOne ratioX ratioY
  separation :
    ∀ M : PolyDTMCandidate,
      DeclaredClockTotal M → ∃ x : BitString, SemanticMismatch M x

def universalLaw_to_separation
    (L : UniversalSeparationLaw) :
    ∀ M : PolyDTMCandidate,
      DeclaredClockTotal M → ∃ x : BitString, SemanticMismatch M x :=
  L.separation

noncomputable def UniversalSeparationLaw.toTerminalLaw
    (L : UniversalSeparationLaw) : TotalCandidateSeparationLaw := by
  classical
  refine
    { witness := fun M =>
        if h : DeclaredClockTotal M then
          Classical.choose (L.separation M h)
        else
          []
      separates := ?_ }
  intro M hTotal
  simp only [dif_pos hTotal]
  exact Classical.choose_spec (L.separation M hTotal)


/-- Converse firewall: once T5F itself is supplied, every geometric/asymptotic
    field of UniversalSeparationLaw is already constructible.  Hence the
    structure is not a weaker producer; its only open mathematical content is
    exactly T5FCore. -/
noncomputable def universalLawOfT5F
    (h : T5FCore) : UniversalSeparationLaw where
  mid := midpoint
  mid_mem := by norm_num [midpoint]
  F := midpointMap
  q := 1 / 2
  contraction := midpointMap_contraction
  repelPull := midpointMap_repelPull
  begin_closed := closedBegin_isClosed
  mid_closed := closedMid_isClosed midpoint
  end_closed := closedEnd_isClosed
  interval_closed := closedInterval_isClosed
  ratio := ratioLaw
  separation := h

theorem universalLaw_iff_t5F :
    Nonempty UniversalSeparationLaw ↔ T5FCore := by
  constructor
  · rintro ⟨L⟩
    exact L.separation
  · intro h
    exact ⟨universalLawOfT5F h⟩

/-- Safe promotion: a law that actually carries the universal separation proof
closes the existing fail-closed terminal gap. -/
theorem universalLaw_closes_t5F
    (L : UniversalSeparationLaw) :
    T5FCore := by
  exact L.separation

/-- A real diagonal compiler is independently sufficient for the same core.
No inhabitant of DiagonalCompilerV2 is manufactured here. -/
theorem diagonalCompiler_closes_t5F
    (D : DiagonalCompilerV2) :
    T5FCore := by
  intro M _
  exact ⟨D.compile M, diagonalCompilerV2_gives_semanticMismatch D M⟩

/-- The clocked semantic transformer only gives a mismatch at x if x is a
literal fixed point. This keeps the already-falsified universal fixed-point
route from being silently reintroduced. -/
theorem semanticDiagonal_fixedPoint_gives_mismatch
    (M : PolyDTMCandidate) (x : BitString)
    (hfix : semanticDiagonalBits M x = x) :
    SemanticMismatch M x := by
  apply self_embed_witness_gives_semanticMismatch M x
  simpa [hfix] using semanticDiagonalBits_flip M x

#print axioms MCore.Real.OpenMathUniversalSeparationLaw.midpointMap_contraction
#print axioms MCore.Real.OpenMathUniversalSeparationLaw.midpointMap_repelPull
#print axioms MCore.Real.OpenMathUniversalSeparationLaw.ratioLaw
#print axioms MCore.Real.OpenMathUniversalSeparationLaw.universalLaw_iff_t5F
#print axioms MCore.Real.OpenMathUniversalSeparationLaw.universalLaw_closes_t5F
#print axioms MCore.Real.OpenMathUniversalSeparationLaw.diagonalCompiler_closes_t5F

end OpenMathUniversalSeparationLaw
end Real
end MCore
