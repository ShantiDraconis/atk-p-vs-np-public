import Mathlib.Computability.PartrecCode
import MCore.Real.P02FinalAttack

namespace MCore
namespace Real
namespace P02KleeneBridge

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02G21G22Attack
open P02WitnessChain
open P02FinalAttack

/-- For one fixed polynomial DTM candidate, an effective diagonal compiler in
Mathlib's partial-recursive code universe. -/
structure EffectiveDiagonalCompiler (M : PolyDTMCandidate) where
  f : Nat.Partrec.Code → ℕ →. ℕ
  partrec : Partrec₂ f

/-- Canonical-SAT realization of a Kleene fixed point.

The hard semantic transport is isolated in flips_of_fixed: once a Mathlib
code c satisfies eval c = K.f c, its canonical SAT bitstring must realize the
negation of M's declared acceptance on that very bitstring. -/
structure CanonicalSATFixedPointRealizer
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) where
  bitsOf : Nat.Partrec.Code → BitString
  valid : ∀ c, CanonicalSATValid (bitsOf c)
  flips_of_fixed :
    ∀ c,
      Nat.Partrec.Code.eval c = K.f c →
        (SATBits circuitBitEncoding (bitsOf c) ↔
          ¬ AcceptsAtDeclaredBound M (bitsOf c))

/-- Mathlib already proves the recursion-theoretic fixed point. -/
theorem kleene_fixed_point
    {M : PolyDTMCandidate}
    (K : EffectiveDiagonalCompiler M) :
    ∃ c : Nat.Partrec.Code,
      Nat.Partrec.Code.eval c = K.f c :=
  Nat.Partrec.Code.fixed_point₂ K.partrec

/-- A computable diagonal compiler plus a canonical-SAT realizer yields one
actual diagonal witness against M. No literal string fixed point is used. -/
noncomputable def witnessFromKleene
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M)
    (R : CanonicalSATFixedPointRealizer M K) :
    DiagonalCounterexampleWitness M :=
  let c := Classical.choose (kleene_fixed_point K)
  let hc := Classical.choose_spec (kleene_fixed_point K)
  { bits := R.bitsOf c
    valid := R.valid c
    flips := by
      have hfixed : Nat.Partrec.Code.eval c = K.f c := hc
      exact R.flips_of_fixed c hfixed }

/-- Uniform bridge required to turn the recursion theorem into the P02
DiagonalFamily. This does not assume G21Pointwise or P02Target. -/
structure D3KleeneSATBridge where
  compiler : ∀ M : PolyDTMCandidate, EffectiveDiagonalCompiler M
  realizer :
    ∀ M : PolyDTMCandidate,
      CanonicalSATFixedPointRealizer M (compiler M)

/-- The recursion theorem discharges the self-reference step once the two
explicit bridges above are supplied. -/
noncomputable def D3KleeneSATBridge.toDiagonalFamily
    (B : D3KleeneSATBridge) :
    DiagonalFamily :=
  { witness := fun M =>
      witnessFromKleene M (B.compiler M) (B.realizer M) }

theorem kleene_sat_bridge_closes_D3
    (B : D3KleeneSATBridge) :
    D3SemanticSelfReference :=
  ⟨B.toDiagonalFamily⟩

theorem kleene_sat_bridge_closes_G21
    (B : D3KleeneSATBridge) :
    G21Pointwise :=
  D3_to_G21Pointwise (kleene_sat_bridge_closes_D3 B)

theorem kleene_sat_bridge_closes_P02
    (B : D3KleeneSATBridge) :
    P02TerminalFrontier.P02Target :=
  D3_to_P02Target (kleene_sat_bridge_closes_D3 B)

/-- The smallest remaining mathematical producer after importing Kleene's
recursion theorem: for every polynomial DTM candidate, supply an effective
diagonal compiler together with a canonical-SAT realization of its Kleene
fixed point. -/
def CanonicalSATKleeneRealizerGap : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ K : EffectiveDiagonalCompiler M,
      Nonempty (CanonicalSATFixedPointRealizer M K)

/-- The exact remaining construction target after importing Kleene's theorem. -/
def D3KleeneSATBridgeGap : Prop :=
  Nonempty D3KleeneSATBridge

/-- The pointwise compiler/realizer producer is sufficient to assemble the
uniform D3 bridge. This theorem adds no mathematical hypothesis beyond the
explicit remaining producer. -/
theorem canonicalSATKleeneRealizerGap_to_D3KleeneSATBridgeGap
    (h : CanonicalSATKleeneRealizerGap) :
    D3KleeneSATBridgeGap := by
  classical
  refine ⟨{
    compiler := fun M => Classical.choose (h M)
    realizer := ?_
  }⟩
  intro M
  exact Classical.choice (Classical.choose_spec (h M))

theorem D3KleeneSATBridgeGap_to_D3
    (h : D3KleeneSATBridgeGap) :
    D3SemanticSelfReference := by
  rcases h with ⟨B⟩
  exact kleene_sat_bridge_closes_D3 B

/-- Consequently the minimal Kleene/SAT producer closes D3 directly. -/
theorem canonicalSATKleeneRealizerGap_to_D3
    (h : CanonicalSATKleeneRealizerGap) :
    D3SemanticSelfReference :=
  D3KleeneSATBridgeGap_to_D3
    (canonicalSATKleeneRealizerGap_to_D3KleeneSATBridgeGap h)

#print axioms kleene_fixed_point
#print axioms witnessFromKleene
#print axioms kleene_sat_bridge_closes_D3
#print axioms kleene_sat_bridge_closes_G21
#print axioms kleene_sat_bridge_closes_P02
#print axioms canonicalSATKleeneRealizerGap_to_D3KleeneSATBridgeGap
#print axioms canonicalSATKleeneRealizerGap_to_D3

end P02KleeneBridge
end Real
end MCore
