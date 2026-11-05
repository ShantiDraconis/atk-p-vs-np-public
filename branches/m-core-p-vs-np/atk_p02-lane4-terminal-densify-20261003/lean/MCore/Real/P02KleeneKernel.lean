import MCore.Real.P02OperatorKernel
import MCore.Real.P02KleeneUniversalBridge

namespace MCore
namespace Real
namespace P02KleeneKernel

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02OperatorKernel

abbrev SATTarget : BitLanguage :=
  SATBits circuitBitEncoding

def DeclaredAccept
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.accepting
      (M.machine.run
        (M.timeBound x.length)
        (initialTMConfig M.machine x)).state = true

/-- Reuse the repository-local self-reference code system. -/
abbrev EffectiveDiagonalCompiler (M : PolyDTMCandidate) :=
  P02KleeneUniversalBridge.EffectiveDiagonalCompiler M

abbrev SATFixedPointRealizer
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) :=
  P02KleeneUniversalBridge.CanonicalSATFixedPointRealizer M K

theorem kleene_fixed_point
    {M : PolyDTMCandidate}
    (K : EffectiveDiagonalCompiler M) :
    ∃ c : K.Code,
      K.eval (K.compile c) = K.eval c :=
  P02KleeneUniversalBridge.kleene_fixed_point K

theorem fixed_flip_fails
    (M : PolyDTMCandidate)
    (x : BitString)
    (hflip : SATTarget x ↔ ¬ DeclaredAccept M x) :
    ¬ M.CorrectAt SATTarget x := by
  intro hCorrect
  change
    M.machine.HaltsWithin
        (M.timeBound x.length)
        (initialTMConfig M.machine x) ∧
      (DeclaredAccept M x ↔ SATTarget x)
    at hCorrect
  rcases hCorrect with ⟨_, hcorr⟩
  by_cases hacc : DeclaredAccept M x
  · have hsat : SATTarget x := hcorr.mp hacc
    exact (hflip.mp hsat) hacc
  · have hsat : SATTarget x := hflip.mpr hacc
    exact hacc (hcorr.mpr hsat)

structure KleeneSATBridge where
  compiler : ∀ M : PolyDTMCandidate, EffectiveDiagonalCompiler M
  realizer :
    ∀ M : PolyDTMCandidate,
      SATFixedPointRealizer M (compiler M)

noncomputable def fixedCode
    (B : KleeneSATBridge)
    (M : PolyDTMCandidate) :
    (B.compiler M).Code :=
  Classical.choose (kleene_fixed_point (B.compiler M))

theorem fixedCode_spec
    (B : KleeneSATBridge)
    (M : PolyDTMCandidate) :
    (B.compiler M).eval
        ((B.compiler M).compile (fixedCode B M)) =
      (B.compiler M).eval (fixedCode B M) :=
  Classical.choose_spec (kleene_fixed_point (B.compiler M))

noncomputable def KleeneSATBridge.toP02Producer
    (B : KleeneSATBridge) :
    CanonicalSATP02Producer := by
  refine
    { counterexample := fun M =>
        (B.realizer M).bitsOf (fixedCode B M)
      sound := ?_ }
  intro M
  apply fixed_flip_fails M
    ((B.realizer M).bitsOf (fixedCode B M))
  simpa [DeclaredAccept, P02KleeneUniversalBridge.DeclaredAccepts] using
    (B.realizer M).flips_of_fixed
      (fixedCode B M) (fixedCode_spec B M)

def KleeneSATBridgeGap : Prop :=
  Nonempty KleeneSATBridge

theorem kleene_bridge_closes_p02
    (h : KleeneSATBridgeGap) :
    Nonempty CanonicalSATP02Producer := by
  rcases h with ⟨B⟩
  exact ⟨B.toP02Producer⟩

theorem kleene_bridge_closes_not_in_p
    (h : KleeneSATBridgeGap) :
    ¬ InP SATTarget := by
  exact canonicalSATProducer_iff_notInP.mp
    (kleene_bridge_closes_p02 h)

#print axioms MCore.Real.P02KleeneKernel.kleene_fixed_point
#print axioms MCore.Real.P02KleeneKernel.fixed_flip_fails
#print axioms MCore.Real.P02KleeneKernel.fixedCode_spec
#print axioms MCore.Real.P02KleeneKernel.kleene_bridge_closes_p02
#print axioms MCore.Real.P02KleeneKernel.kleene_bridge_closes_not_in_p

end P02KleeneKernel
end Real
end MCore
