import MCore.Real.P02KleeneBridge
import MCore.Real.CanonicalCircuitBitsInverse

namespace MCore
namespace Real
namespace P02KleeneCookLevinBridge

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalCircuitBitsInverse
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02G21G22Attack
open P02KleeneBridge

/--
Exact decomposition of the remaining Kleene -> canonical-SAT transport.

This structure does NOT assert G21/P02 and does not contain flips_of_fixed as
a field.  Instead it splits the missing mathematics into:
1. a canonical circuit generated from a recursion-theoretic code,
2. an explicit same-input carrier,
3. a Cook-Levin-style semantic equivalence on that carrier,
4. transport showing that a Kleene fixed point makes the carrier equal to the
   canonical encoded circuit itself.

The last two fields are the only semantic obligations.
-/
structure CookLevinSameInputData
    (M : PolyDTMCandidate)
    (K : EffectiveDiagonalCompiler M) where
  circuitOf : Nat.Partrec.Code → CircuitK1.Circuit
  selfInput : Nat.Partrec.Code → BitString

  cook_levin_correct :
    ∀ c,
      SATTarget (encodeCircuit (circuitOf c)) ↔
        ¬ AcceptsAtDeclaredBound M (selfInput c)

  same_input_of_fixed :
    ∀ c,
      Nat.Partrec.Code.eval c = K.f c →
        selfInput c = encodeCircuit (circuitOf c)

/-- Canonical bits are obtained only from the existing frozen encoder. -/
def CookLevinSameInputData.bitsOf
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (D : CookLevinSameInputData M K)
    (c : Nat.Partrec.Code) : BitString :=
  encodeCircuit (D.circuitOf c)

/-- Validity is closed automatically by the existing canonical encoder. -/
theorem CookLevinSameInputData.valid
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (D : CookLevinSameInputData M K)
    (c : Nat.Partrec.Code) :
    CanonicalSATValid (D.bitsOf c) := by
  refine ⟨D.circuitOf c, ?_⟩
  exact decodeCircuit_encode (D.circuitOf c)

/--
The original flips_of_fixed field follows from exactly:
- Cook-Levin correctness on selfInput c; and
- same-input transport at the Kleene fixed point.

No literal BitString fixed point is used.
-/
theorem CookLevinSameInputData.flips_of_fixed
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (D : CookLevinSameInputData M K)
    (c : Nat.Partrec.Code)
    (hfixed : Nat.Partrec.Code.eval c = K.f c) :
    SATTarget (D.bitsOf c) ↔
      ¬ AcceptsAtDeclaredBound M (D.bitsOf c) := by
  have hsame : D.selfInput c = D.bitsOf c := by
    simpa [CookLevinSameInputData.bitsOf] using
      D.same_input_of_fixed c hfixed
  simpa [hsame] using D.cook_levin_correct c

/-- The decomposed data produces the repository's exact realizer. -/
def CookLevinSameInputData.toCanonicalSATFixedPointRealizer
    {M : PolyDTMCandidate}
    {K : EffectiveDiagonalCompiler M}
    (D : CookLevinSameInputData M K) :
    CanonicalSATFixedPointRealizer M K where
  bitsOf := D.bitsOf
  valid := D.valid
  flips_of_fixed := D.flips_of_fixed

/-- Uniform version matching D3KleeneSATBridge. -/
structure UniformCookLevinSameInputBridge where
  compiler : ∀ M : PolyDTMCandidate, EffectiveDiagonalCompiler M
  data :
    ∀ M : PolyDTMCandidate,
      CookLevinSameInputData M (compiler M)

/-- Once the two explicit semantic obligations are provided uniformly,
the existing D3 bridge is obtained without any further hypothesis. -/
def UniformCookLevinSameInputBridge.toD3KleeneSATBridge
    (B : UniformCookLevinSameInputBridge) :
    D3KleeneSATBridge where
  compiler := B.compiler
  realizer := fun M =>
    (B.data M).toCanonicalSATFixedPointRealizer

theorem uniformCookLevinBridge_closes_G21
    (B : UniformCookLevinSameInputBridge) :
    G21Pointwise :=
  kleene_sat_bridge_closes_G21 B.toD3KleeneSATBridge

theorem uniformCookLevinBridge_closes_P02
    (B : UniformCookLevinSameInputBridge) :
    P02TerminalFrontier.P02Target :=
  kleene_sat_bridge_closes_P02 B.toD3KleeneSATBridge

/-
Fail-closed status:
- canonical encoding/validity: CLOSED here;
- Kleene fixed-point theorem: imported GREEN;
- remaining OPEN_MATH content:
  * cook_levin_correct
  * same_input_of_fixed
No constructor inhabiting UniformCookLevinSameInputBridge is asserted here.
-/

#print axioms MCore.Real.P02KleeneCookLevinBridge.CookLevinSameInputData.valid
#print axioms MCore.Real.P02KleeneCookLevinBridge.CookLevinSameInputData.flips_of_fixed
#print axioms MCore.Real.P02KleeneCookLevinBridge.uniformCookLevinBridge_closes_G21
#print axioms MCore.Real.P02KleeneCookLevinBridge.uniformCookLevinBridge_closes_P02

end P02KleeneCookLevinBridge
end Real
end MCore
