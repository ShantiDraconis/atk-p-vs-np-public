import MCore.Real.P02KleeneCookLevinBridge

namespace MCore
namespace Real
namespace P02FinalProofProducer

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02G21G22Attack
open P02KleeneBridge
open P02KleeneCookLevinBridge

/-- Shared concrete carrier for the two remaining P02 semantic obligations. -/
structure Carrier
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) where
  circuitOf : Nat.Partrec.Code → CircuitK1.Circuit
  selfInput : Nat.Partrec.Code → BitString

def CookLevinCorrect
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (C : Carrier M K) : Prop :=
  ∀ c,
    SATTarget (encodeCircuit (C.circuitOf c)) ↔
      ¬ AcceptsAtDeclaredBound M (C.selfInput c)

def SameInputOfFixed
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (C : Carrier M K) : Prop :=
  ∀ c,
    Nat.Partrec.Code.eval c = K.f c →
      C.selfInput c = encodeCircuit (C.circuitOf c)

def toCookLevinData
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (C : Carrier M K)
    (hCook : CookLevinCorrect C)
    (hSame : SameInputOfFixed C) :
    CookLevinSameInputData M K where
  circuitOf := C.circuitOf
  selfInput := C.selfInput
  cook_levin_correct := hCook
  same_input_of_fixed := hSame

/-- Uniform terminal P02 producer.  These four fields are the whole remaining
clean-lane payload; flips_of_fixed and P02Target are downstream theorems. -/
structure Producer where
  compiler : ∀ M : PolyDTMCandidate, EffectiveDiagonalCompiler M
  carrier : ∀ M : PolyDTMCandidate, Carrier M (compiler M)
  cook_levin_correct :
    ∀ M : PolyDTMCandidate, CookLevinCorrect (carrier M)
  same_input_of_fixed :
    ∀ M : PolyDTMCandidate, SameInputOfFixed (carrier M)

def Producer.toUniformBridge
    (P : Producer) :
    UniformCookLevinSameInputBridge where
  compiler := P.compiler
  data := fun M =>
    toCookLevinData
      (P.carrier M)
      (P.cook_levin_correct M)
      (P.same_input_of_fixed M)

theorem Producer.flips_of_fixed
    (P : Producer)
    (M : PolyDTMCandidate)
    (c : Nat.Partrec.Code)
    (hfixed : Nat.Partrec.Code.eval c = (P.compiler M).f c) :
    SATTarget ((P.toUniformBridge.data M).bitsOf c) ↔
      ¬ AcceptsAtDeclaredBound M ((P.toUniformBridge.data M).bitsOf c) :=
  (P.toUniformBridge.data M).flips_of_fixed c hfixed

theorem Producer.toG21
    (P : Producer) :
    P02G21G22Attack.G21Pointwise :=
  uniformCookLevinBridge_closes_G21 P.toUniformBridge

theorem Producer.toP02Target
    (P : Producer) :
    P02TerminalFrontier.P02Target :=
  uniformCookLevinBridge_closes_P02 P.toUniformBridge

/-
No independent blocker remains after Producer:
compiler + carrier + cook_levin_correct + same_input_of_fixed
-> flips_of_fixed
-> CanonicalSATFixedPointRealizer
-> DiagonalCounterexampleWitness
-> DiagonalFamily
-> G21Pointwise
-> P02Target.
-/

#print axioms MCore.Real.P02FinalProofProducer.Producer.flips_of_fixed
#print axioms MCore.Real.P02FinalProofProducer.Producer.toP02Target

end P02FinalProofProducer
end Real
end MCore
