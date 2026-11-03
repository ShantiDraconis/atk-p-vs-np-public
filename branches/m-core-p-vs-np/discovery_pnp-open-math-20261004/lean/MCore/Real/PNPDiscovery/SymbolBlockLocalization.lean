import MCore.Real.PNPDiscovery.SourceBitVisibilityPressure
import MCore.Real.PNPDiscovery.RightCellInjectivity

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalCircuitBits
open PNPNTMTableauEncoding

/-- Canonical encoded spine for one three-clause symbol assignment block. -/
def encodedSymbolBlock
    (varAt : Option Bool → Nat)
    (target : Option Bool) : BitString :=
  encodeCNFSpinePrefix
    (ntmSetSymbolClauses [] varAt target)

/-- Changing the target symbol only changes polarities, never the total
encoded length of the three singleton clauses. -/
theorem encodedSymbolBlock_length_target_independent
    (varAt : Option Bool → Nat)
    (a b : Option Bool) :
    (encodedSymbolBlock varAt a).length =
      (encodedSymbolBlock varAt b).length := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some bv =>
          cases bv <;>
            simp [encodedSymbolBlock, encodeCNFSpinePrefix,
              ntmSetSymbolClauses, ntmAlphabet, ntmLitFor,
              ntmLiteralCircuit, ntmClauseCircuit, encodeCircuit,
              encodeNat_length]
  | some av =>
      cases av <;>
      cases b with
      | none =>
          simp [encodedSymbolBlock, encodeCNFSpinePrefix,
            ntmSetSymbolClauses, ntmAlphabet, ntmLitFor,
            ntmLiteralCircuit, ntmClauseCircuit, encodeCircuit,
            encodeNat_length]
      | some bv =>
          cases bv <;>
            simp [encodedSymbolBlock, encodeCNFSpinePrefix,
              ntmSetSymbolClauses, ntmAlphabet, ntmLitFor,
              ntmLiteralCircuit, ntmClauseCircuit, encodeCircuit,
              encodeNat_length]

/-- Different target symbols yield different encoded symbol blocks. -/
theorem encodedSymbolBlock_target_injective
    (varAt : Option Bool → Nat) :
    Function.Injective (encodedSymbolBlock varAt) := by
  intro a b h
  by_contra hab
  have hClauses :
      ntmSetSymbolClauses [] varAt a ≠
        ntmSetSymbolClauses [] varAt b := by
    intro hEq
    exact hab (ntmSetSymbolClauses_target_injective varAt hEq)
  exact (unequal_clausePrefixes_give_unequal_spines
    _ _ hClauses) h

/-- Hence a target mismatch produces an actual bit mismatch strictly inside
the common encoded symbol-block length. -/
theorem encodedSymbolBlock_target_mismatch_bit
    (varAt : Option Bool → Nat)
    (a b : Option Bool)
    (hab : a ≠ b) :
    ∃ q : Nat,
      q < (encodedSymbolBlock varAt a).length ∧
      (encodedSymbolBlock varAt a).getD q false ≠
        (encodedSymbolBlock varAt b).getD q false := by
  have hneq :
      encodedSymbolBlock varAt a ≠
        encodedSymbolBlock varAt b := by
    intro h
    exact hab (encodedSymbolBlock_target_injective varAt h)
  have hsep :=
    unequalBitstringsSeparate_closed
      (encodedSymbolBlock varAt a)
      (encodedSymbolBlock varAt b)
      hneq
  rcases hsep with hLen | hBit
  · exact False.elim
      (hLen (encodedSymbolBlock_length_target_independent varAt a b))
  · rcases hBit with ⟨q, hq, hdiff⟩
    refine ⟨q, ?_, hdiff⟩
    have hlen :=
      encodedSymbolBlock_length_target_independent varAt a b
    simpa [hlen] using hq

/-- Instantiated to one right/source cell with aligned layout variable IDs. -/
theorem sourceCell_target_mismatch_localBit
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t i : Nat)
    (hLen : x.length = y.length)
    (hDiff :
      sourceRightSymbol x i ≠
        sourceRightSymbol y i) :
    ∃ q : Nat,
      let vx := ntmRightVar M x t 0 i
      let blockX :=
        encodedSymbolBlock vx (sourceRightSymbol x i)
      let blockY :=
        encodedSymbolBlock vx (sourceRightSymbol y i)
      q < blockX.length ∧
        blockX.getD q false ≠ blockY.getD q false := by
  let vx := ntmRightVar M x t 0 i
  exact encodedSymbolBlock_target_mismatch_bit
    vx
    (sourceRightSymbol x i)
    (sourceRightSymbol y i)
    hDiff

#print axioms MCore.Real.PNPDiscovery.encodedSymbolBlock_length_target_independent
#print axioms MCore.Real.PNPDiscovery.encodedSymbolBlock_target_injective
#print axioms MCore.Real.PNPDiscovery.encodedSymbolBlock_target_mismatch_bit
#print axioms MCore.Real.PNPDiscovery.sourceCell_target_mismatch_localBit

end PNPDiscovery
end Real
end MCore
