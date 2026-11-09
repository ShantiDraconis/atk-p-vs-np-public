import MCore.Real.P02AntiModels
import MCore.Real.P03RangeFailureFrontier
import MCore.Real.P03PerfectFlipDichotomy
import MCore.Real.P03PerfectFlipConstruction
import MCore.Real.P03ClosureKernel

namespace MCore
namespace Real
namespace P03ClosedMath

open CanonicalFinalProof
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02TableauDynamics
open P02OddSemanticRecurrence
open P03OpenMathFrontier
open P03TerminalSemanticBridge
open P03RangeFailureFrontier
open P03PerfectFlipDichotomy
open P03PerfectFlipConstruction
open P03ClosureKernel

/--
Closed-math snapshot for the P03 frontier.

This module contains only already-proved definitions, equivalences,
dichotomies, countermodels, and conditional transports.  It does not inhabit
RemainingOpenMath, RangeFailureLaw, FullRunAcceptanceLaw, or ExistsPerfectFlip.
-/

/-- Pointwise closed dichotomy for every total candidate. -/
theorem candidate_closed_dichotomy
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    RangeFailure M hTotal ∨ PerfectFlip M hTotal := by
  rcases range_failure_or_range_correct M hTotal with hFail | hCorrect
  · exact Or.inl hFail
  · exact Or.inr ((rangeCorrect_iff_perfectFlip M hTotal).1 hCorrect)

/-- Closed equivalence: absence of a range failure is exactly PerfectFlip. -/
theorem no_rangeFailure_iff_perfectFlip
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    ¬ RangeFailure M hTotal ↔ PerfectFlip M hTotal := by
  rw [no_rangeFailure_iff_rangeCorrect M hTotal]
  exact rangeCorrect_iff_perfectFlip M hTotal

/-- Closed global dichotomy: the current universal route or one real perfect flip. -/
theorem global_closed_dichotomy :
    RangeFailureLaw ∨ ExistsPerfectFlip :=
  rangeFailureLaw_or_existsPerfectFlip

/-- Closed global complement law. -/
theorem rangeFailureLaw_iff_not_existsPerfectFlip :
    RangeFailureLaw ↔ ¬ ExistsPerfectFlip := by
  constructor
  · intro hRange hFlip
    exact (existsPerfectFlip_iff_not_rangeFailureLaw.mp hFlip) hRange
  · intro hNoFlip
    by_contra hNoRange
    exact hNoFlip (existsPerfectFlip_iff_not_rangeFailureLaw.mpr hNoRange)

/-- Closed equivalence between the minimal range law and the original P03 law. -/
theorem rangeFailureLaw_iff_fullRunAcceptance :
    RangeFailureLaw ↔ FullRunAcceptanceLaw :=
  rangeFailureLaw_iff_fullRunAcceptanceLaw

/-- Closed transport: if the material A-branch is ever inhabited, the internal
P != NP endpoint follows mechanically. -/
theorem rangeFailureLaw_closes_internal_endpoint
    (H : RangeFailureLaw) :
    PneqNP := by
  have hFull : FullRunAcceptanceLaw :=
    rangeFailureLaw_iff_fullRunAcceptanceLaw.mp H
  exact full_run_acceptance_law_closes_internal_endpoint hFull

/-- Closed transport: a real perfect flip falsifies the current P03 route. -/
theorem perfectFlip_refutes_rangeFailureLaw
    (H : ExistsPerfectFlip) :
    ¬ RangeFailureLaw :=
  existsPerfectFlip_iff_not_rangeFailureLaw.mp H

/-- Closed local consequence: a real perfect flip eliminates every odd
observational recurrence on its concrete R_M orbit. -/
theorem perfectFlip_blocks_odd_recurrence
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (hFlip : PerfectFlip M hTotal)
    (seed : BitString)
    (i d : Nat) :
    ¬ ObsEquiv M
        (Orbit (R_M M hTotal) seed i)
        (Orbit (R_M M hTotal) seed (i + (2 * d + 1))) :=
  perfectFlip_odd_not_equiv hFlip seed i d

/-- Closed structural fact: every real reduction image has the canonical AND
prefix 100. -/
theorem reduction_range_fixed_prefix
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    ∃ tail : BitString,
      R_M M hTotal x = [true, false, false] ++ tail :=
  R_M_fixed_prefix M hTotal x

/-- Closed structural fact: the source is recoverable from every real range
point when the genuine source length and clock are supplied. -/
theorem reduction_range_source_recovery
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    SourceRecovery.decodeSourceBits
        (P02ComplementRunRealization.complementToNTMCandidate M)
        x.length
        (M.timeBound x.length)
        (R_M M hTotal x) = some x :=
  R_M_source_recover M hTotal x

/-- Closed fact: any real deterministic polynomial-time SAT decider would
instantiate the B branch. -/
theorem canonicalSAT_inP_gives_B
    (hP : InP PNPCookLevinMaterialMinCut.CanonicalSAT) :
    ExistsPerfectFlip :=
  canonicalSAT_inP_implies_existsPerfectFlip hP

/-- Closed fail-closed status.  No endpoint is promoted here. -/
theorem closed_math_status :
    P03MaterialLaw.MATERIAL_GAPS = 1 ∧
    P03MaterialLaw.OPEN_BRIDGE = 1 ∧
    P03MaterialLaw.GREEN = false :=
  fail_closed_status_preserved

#print axioms MCore.Real.P03ClosedMath.candidate_closed_dichotomy
#print axioms MCore.Real.P03ClosedMath.no_rangeFailure_iff_perfectFlip
#print axioms MCore.Real.P03ClosedMath.global_closed_dichotomy
#print axioms MCore.Real.P03ClosedMath.rangeFailureLaw_iff_not_existsPerfectFlip
#print axioms MCore.Real.P03ClosedMath.rangeFailureLaw_iff_fullRunAcceptance
#print axioms MCore.Real.P03ClosedMath.rangeFailureLaw_closes_internal_endpoint
#print axioms MCore.Real.P03ClosedMath.perfectFlip_refutes_rangeFailureLaw
#print axioms MCore.Real.P03ClosedMath.perfectFlip_blocks_odd_recurrence
#print axioms MCore.Real.P03ClosedMath.reduction_range_fixed_prefix
#print axioms MCore.Real.P03ClosedMath.reduction_range_source_recovery
#print axioms MCore.Real.P03ClosedMath.canonicalSAT_inP_gives_B
#print axioms MCore.Real.P03ClosedMath.closed_math_status

end P03ClosedMath
end Real
end MCore
