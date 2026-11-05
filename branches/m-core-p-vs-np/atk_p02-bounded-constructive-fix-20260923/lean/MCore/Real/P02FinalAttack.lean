import MCore.Real.P02CanonicalNormalization
import MCore.Real.P02ClockedDiagonalCompiler
import MCore.Real.P02LiteralFixedPointCountermodel
import MCore.Real.P02UniversalWitnessChain
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace P02FinalAttack

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02CanonicalNormalization
open P02DiagonalFrontier
open P02ClockedDiagonalCompiler
open P02LiteralFixedPointCountermodel
open P02G21G22Attack
open P02TerminalFrontier
open P02WitnessChain
open FinalExternalCertificate

/-- D1 is closed: every polynomial candidate admits an explicit monomial clock
with the same machine/accepting predicate and preservation of CorrectAt. -/
theorem D1_candidate_normalization
    (M : PolyDTMCandidate) :
    ∃ coefficient exponent : Nat,
      (normalizedCandidate M coefficient exponent).machine = M.machine ∧
      (normalizedCandidate M coefficient exponent).accepting = M.accepting ∧
      (∀ L : BitLanguage, ∀ x : BitString,
        M.CorrectAt L x →
          (normalizedCandidate M coefficient exponent).CorrectAt L x) :=
  canonical_normalization M

/-- D2 is closed at the semantic-transformer level: for every supplied input,
the canonical SAT output flips the candidate's declared acceptance bit. -/
theorem D2_semantic_flip
    (M : PolyDTMCandidate)
    (x : BitString) :
    SATTarget (semanticDiagonalBits M x) ↔
      ¬ AcceptsAtDeclaredBound M x := by
  exact semanticDiagonalBits_flip M x

/-- The old literal fixed-point route is formally excluded and cannot be used
as the D3 producer. -/
theorem D3_literal_route_rejected :
    ¬ ∀ M : PolyDTMCandidate,
        ∃ x : BitString, semanticDiagonalBits M x = x :=
  no_universal_literal_fixed_point

/-- Exact remaining P02 mathematical producer after D1/D2.
It asks directly for the semantic diagonal witness family, not for a literal
string fixed point. -/
def D3SemanticSelfReference : Prop :=
  Nonempty DiagonalFamily

theorem D3_iff_diagonalFixedPointGap :
    D3SemanticSelfReference ↔ DiagonalFixedPointGap :=
  Iff.rfl

/-- D3 immediately constructs the canonical universal witness producer. -/
theorem D3_to_universalWitnessProducer
    (h : D3SemanticSelfReference) :
    UniversalWitnessProducer :=
  diagonalFixedPointGap_to_universalWitnessExists h

/-- D3 is sufficient for the exact G2.1 pointwise lower-bound statement. -/
theorem D3_to_G21Pointwise
    (h : D3SemanticSelfReference) :
    G21Pointwise :=
  universalWitnessExists_to_g21Pointwise
    (D3_to_universalWitnessProducer h)

/-- D3 is sufficient for the exact P02 target. -/
theorem D3_to_P02Target
    (h : D3SemanticSelfReference) :
    P02Target :=
  universalWitnessExists_to_p02Target
    (D3_to_universalWitnessProducer h)

/-- Internal terminal composition: once P01 and D3 are supplied, PneqNP follows
with no additional P02 hypothesis. -/
theorem P01_D3_to_internal_final
    (hP01 : SATInNPGap circuitBitEncoding)
    (hD3 : D3SemanticSelfReference) :
    PneqNP :=
  p01_p02_close_internal_separation hP01 (D3_to_P02Target hD3)

/-- External terminal composition: the remaining external inputs are exactly
P01, D3, and the already-separated G3 model contract. -/
noncomputable def assembleFinalExternal
    (hP01 : SATInNPGap circuitBitEncoding)
    (hD3 : D3SemanticSelfReference)
    (hG3 : G3ModelMatch.G3ExternalContract) :
    FinalExternalInputs :=
  { g1 := hP01
    g2 := Classical.choice (D3_to_universalWitnessProducer hD3)
    g3 := hG3 }

/-- No extra theorem remains after the three explicit producers are supplied. -/
theorem P01_D3_G3_to_external_final
    (hP01 : SATInNPGap circuitBitEncoding)
    (hD3 : D3SemanticSelfReference)
    (hG3 : G3ModelMatch.G3ExternalContract) :
    FailProofAllGaps.OfficialPneqNP
      hG3.selection.model.P hG3.selection.model.NP :=
  final_external_certificate
    (assembleFinalExternal hP01 hD3 hG3)

#print axioms D1_candidate_normalization
#print axioms D2_semantic_flip
#print axioms D3_literal_route_rejected
#print axioms D3_to_universalWitnessProducer
#print axioms D3_to_G21Pointwise
#print axioms D3_to_P02Target
#print axioms P01_D3_to_internal_final
#print axioms P01_D3_G3_to_external_final

end P02FinalAttack
end Real
end MCore
