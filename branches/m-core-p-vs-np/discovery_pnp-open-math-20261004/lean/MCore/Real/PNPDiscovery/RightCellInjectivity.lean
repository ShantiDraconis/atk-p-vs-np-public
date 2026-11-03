import MCore.Real.PNPDiscovery.SourcePrefixFrontier

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding

/-- The three-clause symbol encoder is injective in its target symbol.
This is finite combinatorics over Option Bool, not complexity theory. -/
theorem ntmSetSymbolClauses_target_injective
    (varAt : Option Bool → Nat) :
    Function.Injective
      (fun target : Option Bool =>
        ntmSetSymbolClauses [] varAt target) := by
  intro a b h
  cases a with
  | none =>
      cases b with
      | none =>
          rfl
      | some bv =>
          cases bv <;>
            simp [ntmSetSymbolClauses, ntmAlphabet,
              ntmLitFor, ntmPos, ntmNeg] at h
  | some av =>
      cases av <;>
        cases b with
        | none =>
            simp [ntmSetSymbolClauses, ntmAlphabet,
              ntmLitFor, ntmPos, ntmNeg] at h
        | some bv =>
            cases bv <;>
              simp [ntmSetSymbolClauses, ntmAlphabet,
                ntmLitFor, ntmPos, ntmNeg] at h ⊢

/-- Close the previously exposed local bridge: once layout variable IDs are
aligned, equality of right-cell blocks forces equality of represented source
symbols. -/
theorem rightCellBlockInjectivity_closed :
    RightCellBlockInjectivity := by
  intro M x y t i hLen hEq
  unfold initialRightCellBlock at hEq
  unfold ntmSetRightCell at hEq
  have hvar :
      (ntmRightVar M x t 0 i) =
        (ntmRightVar M y t 0 i) := by
    funext a
    exact ntmRightVar_eq_of_length_eq M a hLen
  rw [hvar] at hEq
  exact ntmSetSymbolClauses_target_injective
    (ntmRightVar M y t 0 i) hEq

/-- Therefore a first source-prefix break really creates a first differing
encoded right-cell block, with no hidden injectivity assumption. -/
theorem sourcePrefixBreak_gives_block_difference
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t : Nat)
    (hLen : x.length = y.length)
    (B : SourcePrefixBreak x y) :
    initialRightCellBlock M x t B.k ≠
      initialRightCellBlock M y t B.k := by
  intro hEq
  have hSource :=
    rightCellBlockInjectivity_closed
      M x y t B.k hLen hEq
  exact (sourcePrefixBreak_at_boundary x y B) hSource

/-- In the aligned-layout regime, right-cell block equality and source-symbol
equality are now equivalent. -/
theorem rightCellBlock_eq_iff_sourceSymbol_eq
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t i : Nat)
    (hLen : x.length = y.length) :
    initialRightCellBlock M x t i =
        initialRightCellBlock M y t i ↔
      sourceRightSymbol x i =
        sourceRightSymbol y i := by
  constructor
  · exact rightCellBlockInjectivity_closed
      M x y t i hLen
  · intro hSource
    exact initialRightCellBlock_eq
      M x y t t i hLen rfl hSource

#print axioms MCore.Real.PNPDiscovery.ntmSetSymbolClauses_target_injective
#print axioms MCore.Real.PNPDiscovery.rightCellBlockInjectivity_closed
#print axioms MCore.Real.PNPDiscovery.sourcePrefixBreak_gives_block_difference
#print axioms MCore.Real.PNPDiscovery.rightCellBlock_eq_iff_sourceSymbol_eq

end PNPDiscovery
end Real
end MCore
