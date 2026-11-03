import MCore.Real.P02BehavioralAlignment

namespace MCore
namespace Real
namespace P02KleeneGapAudit

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ExactDiagonalFrontier

/-- A deliberately trivial code system.  It witnesses that the code/compiler
fields of CandidateKleeneBridge add no mathematical strength by themselves. -/
def trivialCompiler
    (M : PolyDTMCandidate) :
    EffectiveDiagonalCompiler M where
  Code := Unit
  eval := fun _ n => some n
  compile := fun c => c
  fixed_point := by
    exact ⟨(), rfl⟩

/-- Any exact semantic diagonal witness can be repackaged as the repository's
current CandidateKleeneBridge, with no recursion theorem required. -/
def bridgeOfExactWitness
    {M : PolyDTMCandidate}
    (W : ExactDiagonalWitness M) :
    CandidateKleeneBridge M := by
  rcases W with ⟨x, hFlip⟩
  let K : EffectiveDiagonalCompiler M := trivialCompiler M
  refine
    { compiler := K
      realizer := ?_ }
  refine
    { bitsOf := fun _ => x
      flips_of_fixed := ?_ }
  intro _ _
  exact hFlip

/-- Conversely, a CandidateKleeneBridge already stores the exact semantic
diagonal witness in its realizer field. -/
theorem candidate_bridge_gives_exact_witness
    {M : PolyDTMCandidate}
    (B : CandidateKleeneBridge M) :
    ExactDiagonalWitness M := by
  refine ⟨P02KleeneUniversalBridge.counterexample B, ?_⟩
  have hFlip :=
    B.realizer.flips_of_fixed
      (P02KleeneUniversalBridge.fixedCode B)
      (P02KleeneUniversalBridge.fixedCode_spec B)
  simpa [P02KleeneUniversalBridge.counterexample] using hFlip

/-- Exact audit statement: inhabiting the current Kleene wrapper is equivalent
to inhabiting the semantic diagonal frontier itself. -/
theorem nonempty_candidate_kleene_iff_exact
    (M : PolyDTMCandidate) :
    Nonempty (CandidateKleeneBridge M) ↔
      ExactDiagonalWitness M := by
  constructor
  · rintro ⟨B⟩
    exact candidate_bridge_gives_exact_witness B
  · intro W
    exact ⟨bridgeOfExactWitness W⟩

/-- The same equivalence holds uniformly after restricting to candidates whose
declared clock is total. -/
theorem total_kleene_iff_total_exact :
    TotalCandidateKleeneBridge ↔
      TotalExactDiagonalProducer := by
  constructor
  · intro B M hTotal
    rcases B M hTotal with ⟨K⟩
    exact candidate_bridge_gives_exact_witness K
  · intro B M hTotal
    exact ⟨bridgeOfExactWitness (B M hTotal)⟩

/-- Therefore the old total Kleene gap is exactly the already identified
universal-failure frontier, not an easier independent sublemma. -/
theorem total_kleene_iff_universal_failure :
    TotalCandidateKleeneBridge ↔
      UniversalFailure CanonicalSAT := by
  rw [total_kleene_iff_total_exact]
  exact total_exact_diagonal_iff_universal_failure

#print axioms MCore.Real.P02KleeneGapAudit.candidate_bridge_gives_exact_witness
#print axioms MCore.Real.P02KleeneGapAudit.nonempty_candidate_kleene_iff_exact
#print axioms MCore.Real.P02KleeneGapAudit.total_kleene_iff_total_exact
#print axioms MCore.Real.P02KleeneGapAudit.total_kleene_iff_universal_failure

end P02KleeneGapAudit
end Real
end MCore
