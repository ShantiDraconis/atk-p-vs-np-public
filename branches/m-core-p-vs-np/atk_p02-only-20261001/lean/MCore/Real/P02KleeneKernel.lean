import Mathlib.Computability.PartrecCode
import MCore.Real.P02OperatorKernel

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

/-- Effective code transformer in Mathlib's recursion-theorem universe. -/
structure EffectiveDiagonalCompiler (M : PolyDTMCandidate) where
  compile : Nat.Partrec.Code → Nat.Partrec.Code
  computable : Computable compile

/-- SAT realization of an extensional recursion-theorem fixed point. -/
structure SATFixedPointRealizer
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) where
  bitsOf : Nat.Partrec.Code → BitString
  flip_of_fixed :
    ∀ c,
      (K.compile c).eval = c.eval →
      (SATTarget (bitsOf c) ↔ ¬ DeclaredAccept M (bitsOf c))

theorem kleene_fixed_point
    {M : PolyDTMCandidate}
    (K : EffectiveDiagonalCompiler M) :
    ∃ c : Nat.Partrec.Code,
      (K.compile c).eval = c.eval :=
  Nat.Partrec.Code.fixed_point K.computable

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
    Nat.Partrec.Code :=
  Classical.choose (kleene_fixed_point (B.compiler M))

theorem fixedCode_spec
    (B : KleeneSATBridge)
    (M : PolyDTMCandidate) :
    ((B.compiler M).compile (fixedCode B M)).eval =
      (fixedCode B M).eval :=
  Classical.choose_spec (kleene_fixed_point (B.compiler M))

noncomputable def KleeneSATBridge.toP02Producer
    (B : KleeneSATBridge) :
    CanonicalSATP02Producer := by
  refine
    { counterexample := fun M =>
        (B.realizer M).bitsOf (fixedCode B M)
      sound := ?_ }
  intro M
  exact fixed_flip_fails M
    ((B.realizer M).bitsOf (fixedCode B M))
    ((B.realizer M).flip_of_fixed (fixedCode B M) (fixedCode_spec B M))

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

end P02KleeneKernel
end Real
end MCore
