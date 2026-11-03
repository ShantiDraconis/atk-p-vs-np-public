import MCore.Real.P02ClockedDiagonalCompiler
import MCore.Real.P02DiagonalFrontier
import MCore.Real.P02TerminalFrontier

namespace MCore
namespace Real
namespace P02SelfCodeExistence

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02ClockedDiagonalCompiler

/--
Exact remaining self-code producer.  No endpoint assumption is hidden here:
an inhabitant must supply, for every deterministic polynomial-time candidate,
a canonical SAT input whose SAT truth value flips the candidate's declared
acceptance bit on that same input.
-/
def SelfCodeExistence : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString,
      CanonicalSATValid x ∧
      (SATBits circuitBitEncoding x ↔
        ¬ AcceptsAtDeclaredBound M x)

/-- Package a self-code witness into the already hardened diagonal witness. -/
def diagonalWitnessOfSelfCode
    (M : PolyDTMCandidate)
    (x : BitString)
    (hvalid : CanonicalSATValid x)
    (hflip :
      SATBits circuitBitEncoding x ↔
        ¬ AcceptsAtDeclaredBound M x) :
    DiagonalCounterexampleWitness M :=
  { bits := x
    valid := hvalid
    flips := hflip }

/-- A genuine SelfCodeExistence proof yields the exact diagonal family. -/
noncomputable def diagonalFamilyOfSelfCode
    (h : SelfCodeExistence) :
    DiagonalFamily where
  witness := fun M =>
    let x : BitString := Classical.choose (h M)
    let hs := Classical.choose_spec (h M)
    diagonalWitnessOfSelfCode M x hs.1 hs.2

/-- Promotion only: this theorem does not manufacture self-code existence. -/
theorem self_code_existence_closes_p02
    (h : SelfCodeExistence) :
    P02TerminalFrontier.P02Target :=
  diagonal_family_closes_p02 (diagonalFamilyOfSelfCode h)

/-- Literal semantic fixed points of the existing clocked compiler are a
sufficient, but not assumed, producer of SelfCodeExistence. -/
def SemanticFixedPointExistence : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString,
      semanticDiagonalBits M x = x

theorem semantic_fixed_points_give_self_code
    (h : SemanticFixedPointExistence) :
    SelfCodeExistence := by
  intro M
  rcases h M with ⟨x, hfix⟩
  refine ⟨x, ?_, ?_⟩
  · simpa [hfix] using semanticDiagonalBits_valid M x
  · simpa [hfix] using semanticDiagonalBits_flip M x

#print axioms MCore.Real.P02SelfCodeExistence.diagonalWitnessOfSelfCode
#print axioms MCore.Real.P02SelfCodeExistence.diagonalFamilyOfSelfCode
#print axioms MCore.Real.P02SelfCodeExistence.self_code_existence_closes_p02
#print axioms MCore.Real.P02SelfCodeExistence.semantic_fixed_points_give_self_code

end P02SelfCodeExistence
end Real
end MCore
