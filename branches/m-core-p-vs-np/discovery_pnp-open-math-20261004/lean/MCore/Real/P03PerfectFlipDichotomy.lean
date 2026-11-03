import MCore.Real.P03RangeFailureFrontier

namespace MCore
namespace Real
namespace P03PerfectFlipDichotomy

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02TableauDynamics
open P02OddSemanticRecurrence
open P03RangeFailureFrontier

/-- Existence of one genuine total polynomial candidate whose real Cook--Levin
orbit flips declared acceptance on every reduction edge. -/
def ExistsPerfectFlip : Prop :=
  ∃ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M),
    PerfectFlip M hTotal

/-- A real perfect flip is exactly a counterexample to the universal range
failure law. -/
theorem existsPerfectFlip_iff_not_rangeFailureLaw :
    ExistsPerfectFlip ↔ ¬ RangeFailureLaw := by
  classical
  constructor
  · rintro ⟨M, hTotal, hFlip⟩ hLaw
    have hFail : RangeFailure M hTotal := hLaw M hTotal
    have hCorrect : RangeCorrect M hTotal :=
      (rangeCorrect_iff_perfectFlip M hTotal).2 hFlip
    exact ((no_rangeFailure_iff_rangeCorrect M hTotal).2 hCorrect) hFail
  · intro hNotLaw
    by_contra hNoFlip
    apply hNotLaw
    intro M hTotal
    by_contra hNoFail
    have hCorrect : RangeCorrect M hTotal :=
      (no_rangeFailure_iff_rangeCorrect M hTotal).1 hNoFail
    have hFlip : PerfectFlip M hTotal :=
      (rangeCorrect_iff_perfectFlip M hTotal).1 hCorrect
    exact hNoFlip ⟨M, hTotal, hFlip⟩

/-- Classical global dichotomy: either the current P03 route holds universally,
or one concrete real perfect-flip candidate falsifies it. -/
theorem rangeFailureLaw_or_existsPerfectFlip :
    RangeFailureLaw ∨ ExistsPerfectFlip := by
  classical
  by_cases h : RangeFailureLaw
  · exact Or.inl h
  · exact Or.inr (existsPerfectFlip_iff_not_rangeFailureLaw.2 h)

/-- PerfectFlip gives a genuine one-step semantic flip along the real orbit. -/
theorem perfectFlip_orbit_step
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (hFlip : PerfectFlip M hTotal)
    (seed : BitString)
    (k : Nat) :
    DeclaredAccepts M
        (Orbit (R_M M hTotal) seed (k + 1)) ↔
      ¬ DeclaredAccepts M
        (Orbit (R_M M hTotal) seed k) := by
  simpa [Orbit] using hFlip (Orbit (R_M M hTotal) seed k)

/-- Hence every odd-separated pair on every real orbit is observationally
opposite; this is the concrete counterpart of the abstract anti-model law. -/
theorem perfectFlip_odd_not_equiv
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (hFlip : PerfectFlip M hTotal)
    (seed : BitString)
    (i d : Nat) :
    ¬ ObsEquiv M
        (Orbit (R_M M hTotal) seed i)
        (Orbit (R_M M hTotal) seed (i + (2 * d + 1))) := by
  have hNeg :
      DeclaredAccepts M
          (Orbit (R_M M hTotal) seed (i + (2 * d + 1))) ↔
        ¬ DeclaredAccepts M
          (Orbit (R_M M hTotal) seed i) :=
    odd_flips_negate
      (P := fun k => DeclaredAccepts M (Orbit (R_M M hTotal) seed k))
      (perfectFlip_orbit_step hFlip seed) i d
  intro hEq
  by_cases hAi :
      DeclaredAccepts M (Orbit (R_M M hTotal) seed i)
  · have hAj :
        DeclaredAccepts M
          (Orbit (R_M M hTotal) seed (i + (2 * d + 1))) :=
      hEq.mpr hAi
    exact (hNeg.mp hAj) hAi
  · have hAj :
        DeclaredAccepts M
          (Orbit (R_M M hTotal) seed (i + (2 * d + 1))) :=
      hNeg.mpr hAi
    exact hAi (hEq.mp hAj)

/-- No genuine terminal witness can coexist with PerfectFlip for the same
candidate. -/
theorem perfectFlip_no_fullRunWitness
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (hFlip : PerfectFlip M hTotal) :
    ¬ Nonempty (P03TerminalSemanticBridge.FullRunAcceptanceWitness M hTotal) := by
  intro hW
  have hFail : RangeFailure M hTotal :=
    (rangeFailure_iff_fullRunWitness M hTotal).2 hW
  have hCorrect : RangeCorrect M hTotal :=
    (rangeCorrect_iff_perfectFlip M hTotal).2 hFlip
  exact ((no_rangeFailure_iff_rangeCorrect M hTotal).2 hCorrect) hFail



/--
Any genuine deterministic polynomial-time realization of CanonicalSAT is,
for its own complemented Cook--Levin reduction, a real PerfectFlip candidate.
-/
theorem sat_realization_candidate_perfectFlip
    (D : PolyDTMRealization
      PNPCookLevinMaterialMinCut.CanonicalSAT) :
    ∃ hTotal : DeclaredClockTotal D.candidate,
      PerfectFlip D.candidate hTotal := by
  have hTotal : DeclaredClockTotal D.candidate := by
    intro x
    exact (D.decides x).1
  refine ⟨hTotal, ?_⟩
  intro x
  have hx :
      DeclaredAccepts D.candidate x ↔
        PNPCookLevinMaterialMinCut.CanonicalSAT x := by
    exact (D.decides x).2
  have hy :
      DeclaredAccepts D.candidate
          (R_M D.candidate hTotal x) ↔
        PNPCookLevinMaterialMinCut.CanonicalSAT
          (R_M D.candidate hTotal x) := by
    exact (D.decides (R_M D.candidate hTotal x)).2
  have hreduce :
      PNPCookLevinMaterialMinCut.CanonicalSAT
          (R_M D.candidate hTotal x) ↔
        ¬ DeclaredAccepts D.candidate x := by
    simpa [R_M] using
      complement_reduce_correct D.candidate hTotal x
  exact hy.trans hreduce

theorem canonicalSAT_inP_implies_existsPerfectFlip
    (hP : InP PNPCookLevinMaterialMinCut.CanonicalSAT) :
    ExistsPerfectFlip := by
  rcases hP with ⟨D⟩
  rcases sat_realization_candidate_perfectFlip D with
    ⟨hTotal, hFlip⟩
  exact ⟨D.candidate, hTotal, hFlip⟩

/--
Consequently the universal range-failure route excludes a deterministic
polynomial-time CanonicalSAT decider, consistently with its downstream
UniversalFailure theorem.
-/
theorem rangeFailureLaw_implies_canonicalSAT_not_inP
    (H : RangeFailureLaw) :
    ¬ InP PNPCookLevinMaterialMinCut.CanonicalSAT := by
  intro hP
  have hFlip : ExistsPerfectFlip :=
    canonicalSAT_inP_implies_existsPerfectFlip hP
  exact (existsPerfectFlip_iff_not_rangeFailureLaw.mp hFlip) H

#print axioms MCore.Real.P03PerfectFlipDichotomy.sat_realization_candidate_perfectFlip
#print axioms MCore.Real.P03PerfectFlipDichotomy.canonicalSAT_inP_implies_existsPerfectFlip
#print axioms MCore.Real.P03PerfectFlipDichotomy.rangeFailureLaw_implies_canonicalSAT_not_inP

#print axioms MCore.Real.P03PerfectFlipDichotomy.existsPerfectFlip_iff_not_rangeFailureLaw
#print axioms MCore.Real.P03PerfectFlipDichotomy.rangeFailureLaw_or_existsPerfectFlip
#print axioms MCore.Real.P03PerfectFlipDichotomy.perfectFlip_orbit_step
#print axioms MCore.Real.P03PerfectFlipDichotomy.perfectFlip_odd_not_equiv
#print axioms MCore.Real.P03PerfectFlipDichotomy.perfectFlip_no_fullRunWitness

end P03PerfectFlipDichotomy
end Real
end MCore
