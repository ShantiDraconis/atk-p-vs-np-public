import MCore.Real.P02UniversalFailureMinCut

namespace MCore
namespace Real
namespace P02KleeneUniversalBridge

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02UniversalFailureMinCut

/-- Candidate's declared acceptance proposition at its own certified clock. -/
def DeclaredAccepts
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.accepting
      (M.machine.run
        (M.timeBound x.length)
        (initialTMConfig M.machine x)).state = true

/-- Local self-reference code system. The repository has no Mathlib
computability dependency, so code/evaluation/self-reference are explicit data
rather than an unavailable imported theorem. -/
structure EffectiveDiagonalCompiler (M : PolyDTMCandidate) where
  Code : Type
  eval : Code → Nat → Option Nat
  compile : Code → Code
  fixed_point :
    ∃ c : Code, eval (compile c) = eval c

/-- Transport from a code fixed point into the exact canonical SAT language.
This is the genuine semantic realizer obligation. -/
structure CanonicalSATFixedPointRealizer
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) where
  bitsOf : K.Code → BitString
  flips_of_fixed :
    ∀ c : K.Code,
      (K.eval (K.compile c) = K.eval c) →
        (CanonicalSAT (bitsOf c) ↔
          ¬ DeclaredAccepts M (bitsOf c))

theorem kleene_fixed_point
    {M : PolyDTMCandidate}
    (K : EffectiveDiagonalCompiler M) :
    ∃ c : K.Code,
      K.eval (K.compile c) = K.eval c :=
  K.fixed_point

/-- Per-candidate package required to turn self-reference into a canonical SAT
counterexample. -/
structure CandidateKleeneBridge (M : PolyDTMCandidate) where
  compiler : EffectiveDiagonalCompiler M
  realizer : CanonicalSATFixedPointRealizer M compiler

noncomputable def fixedCode
    {M : PolyDTMCandidate}
    (B : CandidateKleeneBridge M) :
    B.compiler.Code :=
  Classical.choose (kleene_fixed_point B.compiler)

theorem fixedCode_spec
    {M : PolyDTMCandidate}
    (B : CandidateKleeneBridge M) :
    B.compiler.eval (B.compiler.compile (fixedCode B)) =
      B.compiler.eval (fixedCode B) :=
  Classical.choose_spec (kleene_fixed_point B.compiler)

noncomputable def counterexample
    {M : PolyDTMCandidate}
    (B : CandidateKleeneBridge M) :
    BitString :=
  B.realizer.bitsOf (fixedCode B)

/-- A code-level fixed point plus the semantic SAT realizer produces a genuine
failure of the original candidate at one concrete input. -/
theorem counterexample_fails
    {M : PolyDTMCandidate}
    (B : CandidateKleeneBridge M) :
    ¬ M.CorrectAt CanonicalSAT (counterexample B) := by
  have hfix :
      B.compiler.eval (B.compiler.compile (fixedCode B)) =
        B.compiler.eval (fixedCode B) :=
    fixedCode_spec B
  have hflip :
      CanonicalSAT (counterexample B) ↔
        ¬ DeclaredAccepts M (counterexample B) := by
    change
      CanonicalSAT (B.realizer.bitsOf (fixedCode B)) ↔
        ¬ DeclaredAccepts M (B.realizer.bitsOf (fixedCode B))
    exact CanonicalSATFixedPointRealizer.flips_of_fixed
      B.realizer
      (fixedCode B)
      hfix
  intro hCorrect
  unfold PolyDTMCandidate.CorrectAt at hCorrect
  dsimp at hCorrect
  rcases hCorrect with ⟨_, hSem0⟩
  have hSem :
      DeclaredAccepts M (counterexample B) ↔
        CanonicalSAT (counterexample B) := by
    exact hSem0
  by_cases hAcc : DeclaredAccepts M (counterexample B)
  · have hSat : CanonicalSAT (counterexample B) :=
      hSem.mp hAcc
    exact (hflip.mp hSat) hAcc
  · have hSat : CanonicalSAT (counterexample B) :=
      hflip.mpr hAcc
    exact hAcc (hSem.mpr hSat)

/-- Uniform non-literal self-reference bridge. No UniversalFailure/not-InP
field is stored here. -/
structure KleeneUniversalBridge where
  bridge : ∀ M : PolyDTMCandidate, CandidateKleeneBridge M

noncomputable def KleeneUniversalBridge.toProducer
    (B : KleeneUniversalBridge) :
    UniversalCounterexampleProducer where
  counterexample := fun M => counterexample (B.bridge M)
  failure := by
    intro M
    apply (failureMode_iff_not_correctAt
      M (counterexample (B.bridge M))).mpr
    exact counterexample_fails (B.bridge M)

theorem kleene_bridge_implies_universal_failure
    (B : KleeneUniversalBridge) :
    UniversalFailure CanonicalSAT :=
  producer_implies_universal_failure B.toProducer

theorem kleene_bridge_closes_internal_endpoint
    (B : KleeneUniversalBridge) :
    PneqNP :=
  producer_closes_internal_endpoint B.toProducer

abbrev KleeneUniversalBridgeGap : Prop :=
  Nonempty KleeneUniversalBridge

#print axioms MCore.Real.P02KleeneUniversalBridge.kleene_fixed_point
#print axioms MCore.Real.P02KleeneUniversalBridge.counterexample_fails
#print axioms MCore.Real.P02KleeneUniversalBridge.KleeneUniversalBridge.toProducer
#print axioms MCore.Real.P02KleeneUniversalBridge.kleene_bridge_implies_universal_failure
#print axioms MCore.Real.P02KleeneUniversalBridge.kleene_bridge_closes_internal_endpoint

end P02KleeneUniversalBridge
end Real
end MCore
