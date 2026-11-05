import MCore.Real.P02LiteralFixedPointCountermodel

namespace MCore
namespace Real
namespace G21NegativeFinalCertificate

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02ClockedDiagonalCompiler
open P02LiteralFixedPointFirewall
open P02LiteralFixedPointCountermodel

/-- Canonical proposition for the literal universal fixed-point formulation
that was falsified by the certified P02 countermodel lane. -/
abbrev LiteralFixedPointFormulation : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString, semanticDiagonalBits M x = x

/-- Final negative theorem for the literal fixed-point formulation.
This theorem closes only the literal formulation lane. It does not by itself
prove the semantic G21 replacement or the official P != NP endpoint. -/
theorem G21_literal_fixed_point_falsified :
    ¬ LiteralFixedPointFormulation := by
  exact P02LiteralFixedPointCountermodel.no_universal_literal_fixed_point

/-- Any larger claim whose assumptions include the falsified literal
formulation is inconsistent. -/
theorem G21_literal_fixed_point_claim_contradiction
    (P_alegado : Prop) :
    LiteralFixedPointFormulation ∧ P_alegado → False := by
  rintro ⟨hLiteral, _⟩
  exact G21_literal_fixed_point_falsified hLiteral

/-- Machine-readable theorem metadata retained inside the kernel source.
These strings carry no mathematical force. -/
def theoremId : String := "PNP_G21"
def gapClass : String := "F_FORMULATION"
def theoremStatus : String := "FALSIFIED_FORMULATION"
def terminalState : String := "CLOSED_BY_FALSIFICATION"
def pendingHypotheses : List String := []
def replacementRoute : String := "Semantic Self-Embedding / G21 semantic route"

#print axioms MCore.Real.G21NegativeFinalCertificate.G21_literal_fixed_point_falsified
#print axioms MCore.Real.G21NegativeFinalCertificate.G21_literal_fixed_point_claim_contradiction

end G21NegativeFinalCertificate
end Real
end MCore
