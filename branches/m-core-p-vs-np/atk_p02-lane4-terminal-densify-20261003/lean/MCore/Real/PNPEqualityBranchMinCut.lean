
import MCore.Real.P02TwoSidedOrientation
import MCore.BackwardAudit.ClosedDiscriminant

namespace MCore
namespace Real
namespace PNPEqualityBranchMinCut

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open ClosedDiscriminant
open P02TwoSidedOrientation

abbrev CanonicalSAT : BitLanguage :=
  SATBits circuitBitEncoding

/--
Exact remaining bridge for the equality branch.

It is intentionally stated only as the missing semantic transfer:
if canonical SAT is in P, then every language in NP is in P in the same
canonical machine model.  No equality endpoint is stored as a field.
-/
structure CanonicalSATCompletenessTransfer where
  np_to_p_of_sat_in_p :
    InP CanonicalSAT ->
      ∀ L : BitLanguage, InNP L -> InP L

/-- Canonical P subset NP, already available in the repository, plus the
missing reverse inclusion gives extensional equality of P and NP. -/
theorem sat_in_p_closes_equality
    (T : CanonicalSATCompletenessTransfer)
    (hSAT : InP CanonicalSAT)
    (hPsubNP : ∀ L : BitLanguage, InP L -> InNP L) :
    ∀ L : BitLanguage, InP L ↔ InNP L := by
  intro L
  constructor
  · exact hPsubNP L
  · exact T.np_to_p_of_sat_in_p hSAT L

/--
Two-sided final orientation in the canonical model.
The separation branch is already material once UniversalFailure is supplied.
The equality branch has exactly one remaining mathematical producer:
CanonicalSATCompletenessTransfer.
-/
inductive PNPFinalOrientation
    (T : CanonicalSATCompletenessTransfer)
    (hPsubNP : ∀ L : BitLanguage, InP L -> InNP L) : Type where
  | separation :
      PneqNP ->
      PNPFinalOrientation T hPsubNP
  | equality :
      (∀ L : BitLanguage, InP L ↔ InNP L) ->
      PNPFinalOrientation T hPsubNP

theorem orient_from_canonicalSAT
    (T : CanonicalSATCompletenessTransfer)
    (hPsubNP : ∀ L : BitLanguage, InP L -> InNP L) :
    Nonempty (PNPFinalOrientation T hPsubNP) := by
  rcases canonicalSATOrientation_total with ⟨o⟩
  cases o with
  | lowerBound hFail =>
      exact ⟨.separation (lowerBound_branch_closes_pneqnp hFail)⟩
  | polynomial hSAT =>
      exact ⟨.equality (sat_in_p_closes_equality T hSAT hPsubNP)⟩

/--
No logical residue remains after the single equality-branch transfer.
-/
def PNP_EQUALITY_BRANCH_OPEN_MATH : Prop :=
  Nonempty CanonicalSATCompletenessTransfer

#print axioms MCore.Real.PNPEqualityBranchMinCut.sat_in_p_closes_equality
#print axioms MCore.Real.PNPEqualityBranchMinCut.orient_from_canonicalSAT

end PNPEqualityBranchMinCut
end Real
end MCore
