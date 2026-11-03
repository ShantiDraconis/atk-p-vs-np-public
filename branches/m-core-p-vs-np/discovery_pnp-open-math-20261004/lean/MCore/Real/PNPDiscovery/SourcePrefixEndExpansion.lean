import MCore.Real.PNPDiscovery.SourceCellBitTransportClosed

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding

/-- Exact encoded length of one positive literal. -/
theorem encode_ntmPos_literal_length
    (v : Nat) :
    (encodeCircuit (ntmLiteralCircuit (ntmPos v))).length = v + 4 := by
  simp [ntmLiteralCircuit, ntmPos, encodeCircuit, encodeNat_length]

/-- Exact encoded length of one negative literal. -/
theorem encode_ntmNeg_literal_length
    (v : Nat) :
    (encodeCircuit (ntmLiteralCircuit (ntmNeg v))).length = v + 7 := by
  simp [ntmLiteralCircuit, ntmNeg, encodeCircuit, encodeNat_length]

/-- Exact encoded length of a singleton positive clause. -/
theorem encode_singleton_pos_clause_length
    (v : Nat) :
    (encodeCircuit (ntmClauseCircuit [ntmPos v])).length = v + 10 := by
  simp [ntmClauseCircuit, encodeCircuit,
    encode_ntmPos_literal_length]

/-- Exact encoded length of a singleton negative clause. -/
theorem encode_singleton_neg_clause_length
    (v : Nat) :
    (encodeCircuit (ntmClauseCircuit [ntmNeg v])).length = v + 13 := by
  simp [ntmClauseCircuit, encodeCircuit,
    encode_ntmNeg_literal_length]

/-- One clause contributes a 3-bit AND spine tag before its own circuit. -/
def encodedSingletonSpineLength
    (l : NTMLiteral) : Nat :=
  3 + (encodeCircuit (ntmClauseCircuit [l])).length

@[simp] theorem encodedSingletonSpineLength_pos
    (v : Nat) :
    encodedSingletonSpineLength (ntmPos v) = v + 13 := by
  simp [encodedSingletonSpineLength,
    encode_singleton_pos_clause_length]

@[simp] theorem encodedSingletonSpineLength_neg
    (v : Nat) :
    encodedSingletonSpineLength (ntmNeg v) = v + 16 := by
  simp [encodedSingletonSpineLength,
    encode_singleton_neg_clause_length]

/-- Exact encoded symbol-block length.  Exactly one of the three singleton
clauses is positive and the other two are negative. -/
theorem encodedSymbolBlock_length_exact
    (varAt : Option Bool → Nat)
    (target : Option Bool) :
    (encodedSymbolBlock varAt target).length =
      varAt none + varAt (some false) + varAt (some true) + 45 := by
  cases target with
  | none =>
      simp [encodedSymbolBlock, encodeCNFSpinePrefix,
        ntmSetSymbolClauses, ntmAlphabet, ntmLitFor,
        encodedSingletonSpineLength,
        encodeCircuit, ntmClauseCircuit, ntmLiteralCircuit,
        encodeNat_length]
      omega
  | some b =>
      cases b <;>
        simp [encodedSymbolBlock, encodeCNFSpinePrefix,
          ntmSetSymbolClauses, ntmAlphabet, ntmLitFor,
          encodedSingletonSpineLength,
          encodeCircuit, ntmClauseCircuit, ntmLiteralCircuit,
          encodeNat_length] <;>
        omega

/-- Consecutive variable IDs B,B+1,B+2 give the simple closed form 3B+48. -/
theorem encodedSymbolBlock_consecutive_length
    (B : Nat)
    (target : Option Bool) :
    (encodedSymbolBlock
      (fun a => B + ntmSymbolCode a)
      target).length =
      3 * B + 48 := by
  rw [encodedSymbolBlock_length_exact]
  simp [ntmSymbolCode]
  omega

/-- Time-zero head block starts at ntmHeadBase and therefore has exact size. -/
theorem encoded_initialHeadBlock_length
    (M : PolyNTMCandidate)
    (t : Nat)
    (target : Option Bool) :
    (encodedSymbolBlock
      (ntmHeadVar M t 0)
      target).length =
      3 * ntmHeadBase M t + 48 := by
  apply encodedSymbolBlock_consecutive_length
    (ntmHeadBase M t)
    target

/-- Time-zero right cell i starts at base + 3*i. -/
theorem encoded_initialRightCell_length
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (target : Option Bool) :
    (encodedSymbolBlock
      (ntmRightVar M x t 0 i)
      target).length =
      3 * (ntmRightBase M x t + 3 * i) + 48 := by
  have hvar :
      ntmRightVar M x t 0 i =
        fun a => (ntmRightBase M x t + 3 * i) +
          ntmSymbolCode a := by
    funext a
    simp [ntmRightVar]
    omega
  rw [hvar]
  exact encodedSymbolBlock_consecutive_length
    (ntmRightBase M x t + 3 * i)
    target

/-- Same exact formula for one time-zero left cell. -/
theorem encoded_initialLeftCell_length
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (target : Option Bool) :
    (encodedSymbolBlock
      (ntmLeftVar M x t 0 i)
      target).length =
      3 * (ntmLeftBase M x t + 3 * i) + 48 := by
  have hvar :
      ntmLeftVar M x t 0 i =
        fun a => (ntmLeftBase M x t + 3 * i) +
          ntmSymbolCode a := by
    funext a
    simp [ntmLeftVar]
    omega
  rw [hvar]
  exact encodedSymbolBlock_consecutive_length
    (ntmLeftBase M x t + 3 * i)
    target

#print axioms MCore.Real.PNPDiscovery.encodedSymbolBlock_length_exact
#print axioms MCore.Real.PNPDiscovery.encodedSymbolBlock_consecutive_length
#print axioms MCore.Real.PNPDiscovery.encoded_initialHeadBlock_length
#print axioms MCore.Real.PNPDiscovery.encoded_initialRightCell_length
#print axioms MCore.Real.PNPDiscovery.encoded_initialLeftCell_length

end PNPDiscovery
end Real
end MCore
