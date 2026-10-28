import MCore.Real.CanonicalCircuitBits
import MCore.Real.P01GuessedWitnessRelation

namespace MCore
namespace Real
namespace P01RawDecodeClassification

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits

/-- Exact semantic classification of one bounded decoder run.  Success carries
the decoded circuit and exact residual tail; failure records decoder failure.
This is not an assumption and carries no endpoint proposition. -/
inductive DecodeCoreClass (fuel : Nat) (bits : BitString) : Type
  | success (phi : Circuit) (tail : BitString)
      (h : decodeCircuitCore fuel bits = some (phi, tail))
  | failure (h : decodeCircuitCore fuel bits = none)

/-- Every bounded decoder call is constructively classified. -/
def classifyDecodeCore (fuel : Nat) (bits : BitString) :
    DecodeCoreClass fuel bits := by
  cases h : decodeCircuitCore fuel bits with
  | none =>
      exact .failure h
  | some p =>
      rcases p with ⟨phi, tail⟩
      exact .success phi tail h

/-- Whole-source classification: either exactly one canonical circuit was
decoded with no residual tail, or the whole-source decoder fails. -/
inductive DecodeWholeClass (bits : BitString) : Type
  | canonical (phi : Circuit)
      (h : decodeCircuit bits = some phi)
  | malformed (h : decodeCircuit bits = none)

/-- Total classification of raw source bits by the repository's actual decoder. -/
def classifyDecodeWhole (bits : BitString) : DecodeWholeClass bits := by
  cases h : decodeCircuit bits with
  | none =>
      exact .malformed h
  | some phi =>
      exact .canonical phi h

theorem canonical_is_exact_encoding
    {bits : BitString} {phi : Circuit}
    (h : decodeCircuit bits = some phi) :
    bits = encodeCircuit phi :=
  P01GuessedWitnessRelation.decodeCircuit_sound bits phi h

#print axioms MCore.Real.P01RawDecodeClassification.classifyDecodeCore
#print axioms MCore.Real.P01RawDecodeClassification.classifyDecodeWhole
#print axioms MCore.Real.P01RawDecodeClassification.canonical_is_exact_encoding

end P01RawDecodeClassification
end Real
end MCore
