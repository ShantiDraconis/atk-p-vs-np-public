import Mathlib.Computability.PartrecCode
import MCore.Real.P02FinalAttack

namespace MCore
namespace Real
namespace P02KleeneSelfReferenceBridge

open CanonicalFinalProof
open P02DiagonalFrontier
open P02FinalAttack

/-- Mathlib already proves the recursion-theoretic fixed-point theorem.
This wrapper pins the exact theorem used by the P02 attack. -/
theorem kleene_fixed_point
    {f : Nat.Partrec.Code → Nat.Partrec.Code}
    (hf : Computable f) :
    ∃ c : Nat.Partrec.Code, (f c).eval = c.eval :=
  Nat.Partrec.Code.fixed_point hf

/--
Exact remaining adapter from recursion-theoretic self-reference to the
repository's canonical SAT diagonal witness.

The hard content is deliberately exposed as fields:
* a code transformer for each polynomial DTM candidate;
* computability of that transformer;
* a semantics bridge turning extensional code equality into an actual
  canonical-SAT diagonal witness for that same candidate.

No P02 endpoint proposition is stored as a field.
-/
structure KleeneToSATBridge where
  compile :
    PolyDTMCandidate → Nat.Partrec.Code → Nat.Partrec.Code
  compile_computable :
    ∀ M : PolyDTMCandidate, Computable (compile M)
  self_semantics_to_diagonal :
    ∀ (M : PolyDTMCandidate) (c : Nat.Partrec.Code),
      (compile M c).eval = c.eval →
        DiagonalCounterexampleWitness M

/-- Once the computable-code-to-SAT bridge exists, Mathlib's fixed-point
theorem supplies one diagonal witness for every polynomial candidate. -/
noncomputable def KleeneToSATBridge.toDiagonalFamily
    (B : KleeneToSATBridge) :
    DiagonalFamily where
  witness := fun M =>
    let h := kleene_fixed_point (B.compile_computable M)
    let c := Classical.choose h
    B.self_semantics_to_diagonal M c (Classical.choose_spec h)

/-- The exact D3 producer reduces to the Kleene-to-canonical-SAT bridge. -/
theorem kleene_bridge_closes_D3
    (B : KleeneToSATBridge) :
    D3SemanticSelfReference :=
  ⟨B.toDiagonalFamily⟩

theorem kleene_bridge_closes_G21
    (B : KleeneToSATBridge) :
    P02G21G22Attack.G21Pointwise :=
  D3_to_G21Pointwise (kleene_bridge_closes_D3 B)

theorem kleene_bridge_closes_P02
    (B : KleeneToSATBridge) :
    P02TerminalFrontier.P02Target :=
  D3_to_P02Target (kleene_bridge_closes_D3 B)

#print axioms kleene_fixed_point
#print axioms kleene_bridge_closes_D3
#print axioms kleene_bridge_closes_G21
#print axioms kleene_bridge_closes_P02

end P02KleeneSelfReferenceBridge
end Real
end MCore
