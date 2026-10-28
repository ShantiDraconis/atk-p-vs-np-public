
import MCore.Real.P02UniversalFailureMinCut
import MCore.Real.P01PostMinCutClosure

namespace MCore
namespace Real
namespace P02TwoSidedOrientation

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02UniversalFailureMinCut
open P01PostMinCutClosure

abbrev CanonicalSAT : BitLanguage :=
  SATBits circuitBitEncoding

/--
The exact negative branch of UniversalFailure is polynomial decidability.
This is classical double-negation elimination applied to the already-proved
UniversalFailure <-> not InP equivalence.
-/
theorem not_universalFailure_iff_inP :
    (¬ UniversalFailure CanonicalSAT) ↔ InP CanonicalSAT := by
  constructor
  · intro hNoFail
    apply Classical.byContradiction
    intro hNotP
    exact hNoFail (not_in_p_implies_universal_failure hNotP)
  · intro hP hFail
    exact (universal_failure_implies_not_in_p hFail) hP

/--
A material two-sided orientation for canonical SAT.
The positive branch carries the lower bound; the negative branch carries an
actual polynomial deterministic realization of canonical SAT.
-/
inductive CanonicalSATOrientation : Type where
  | lowerBound :
      UniversalFailure CanonicalSAT ->
      CanonicalSATOrientation
  | polynomial :
      InP CanonicalSAT ->
      CanonicalSATOrientation

theorem canonicalSATOrientation_total :
    Nonempty CanonicalSATOrientation := by
  rcases Classical.em (UniversalFailure CanonicalSAT) with hFail | hNoFail
  · exact ⟨.lowerBound hFail⟩
  · exact ⟨.polynomial (not_universalFailure_iff_inP.mp hNoFail)⟩

/--
The lower-bound branch closes the internal separation endpoint using the
already recovered canonical SAT-in-NP result.
-/
theorem lowerBound_branch_closes_pneqnp
    (hFail : UniversalFailure CanonicalSAT) :
    PneqNP :=
  target_failure_implies_p_ne_np
    canonical_sat_in_np_closed
    hFail

/--
The polynomial branch exposes the exact concrete object required by any
future NP-completeness transfer: a deterministic polynomial-time realization
of canonical SAT.
-/
theorem polynomial_branch_exposes_realization
    (hP : InP CanonicalSAT) :
    Nonempty (PolyDTMRealization CanonicalSAT) :=
  hP

/--
Branch semantics: every canonical orientation carries genuine mathematical
content.  No branch is fabricated from a mere status tag.
-/
def CanonicalSATOrientation.Semantics : CanonicalSATOrientation -> Prop
  | .lowerBound _ => PneqNP
  | .polynomial _ => InP CanonicalSAT

theorem canonicalSATOrientation_sound
    (o : CanonicalSATOrientation) :
    o.Semantics := by
  cases o with
  | lowerBound h =>
      exact lowerBound_branch_closes_pneqnp h
  | polynomial h =>
      exact h

#print axioms MCore.Real.P02TwoSidedOrientation.not_universalFailure_iff_inP
#print axioms MCore.Real.P02TwoSidedOrientation.canonicalSATOrientation_total
#print axioms MCore.Real.P02TwoSidedOrientation.lowerBound_branch_closes_pneqnp
#print axioms MCore.Real.P02TwoSidedOrientation.canonicalSATOrientation_sound

end P02TwoSidedOrientation
end Real
end MCore
