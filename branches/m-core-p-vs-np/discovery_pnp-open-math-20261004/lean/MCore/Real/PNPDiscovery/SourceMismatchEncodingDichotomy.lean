import MCore.Real.PNPDiscovery.SourceMismatchVisibility

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding

/-- Generic finite-list separation: unequal lists either have unequal lengths,
or differ at some index below their common minimum length. -/
def PrefixMismatchDichotomy (a b : BitString) : Prop :=
  a.length ≠ b.length ∨
    ∃ q : Nat,
      q < Nat.min a.length b.length ∧
      a.getD q false ≠ b.getD q false

/-- Encoded CNF spines for unequal clause prefixes cannot be equal, because
appending the common terminal true-CNF encoding would contradict injectivity
of the full canonical CNF encoding. -/
theorem unequal_clausePrefixes_give_unequal_spines
    (F G : NTMCNF)
    (hFG : F ≠ G) :
    encodeCNFSpinePrefix F ≠
      encodeCNFSpinePrefix G := by
  intro hSpine
  have hEnc :
      encodeCircuit (ntmCNFCircuit F) =
        encodeCircuit (ntmCNFCircuit G) := by
    rw [encode_ntmCNFCircuit_split_at F F.length]
    rw [encode_ntmCNFCircuit_split_at G G.length]
    simp [hSpine]
  exact hFG (encode_ntmCNFCircuit_injective hEnc)

/-- Exact source-mismatch encoding frontier.  The only possibilities left are
a boundary-length mismatch or an actual bit mismatch before the shorter
boundary. -/
def SourceMismatchEncodingDichotomy : Prop :=
  ∀ (M : PolyDTMCandidate)
    (x y : BitString)
    (j : Nat),
    x.length = y.length →
    M.timeBound x.length = M.timeBound y.length →
    sourceHeadSymbol x = sourceHeadSymbol y →
    SourceRightPrefixAligned x y j →
    sourceRightSymbol x j ≠ sourceRightSymbol y j →
    j + 1 ≤ ntmRadius x (M.timeBound x.length) →
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    let cend := sourcePrefixClauseEnd N x tx (j + 1)
    let Fx := boundedExecTableauCNF_NTM N x tx
    let Fy := boundedExecTableauCNF_NTM N y ty
    let sx := encodeCNFSpinePrefix (Fx.take cend)
    let sy := encodeCNFSpinePrefix (Fy.take cend)
    PrefixMismatchDichotomy sx sy

/-- What remains to close SourceMismatchEncodingDichotomy is now purely a
generic list fact: unequal finite bitstrings satisfy PrefixMismatchDichotomy. -/
def UnequalBitstringsSeparate : Prop :=
  ∀ a b : BitString,
    a ≠ b →
      PrefixMismatchDichotomy a b

theorem unequalBitstringsSeparate_closes_sourceEncoding
    (Hsep : UnequalBitstringsSeparate) :
    SourceMismatchEncodingDichotomy := by
  intro M x y j hLen hClock hHead hPrev hDiff hRadius
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  let cend := sourcePrefixClauseEnd N x tx (j + 1)
  let Fx := boundedExecTableauCNF_NTM N x tx
  let Fy := boundedExecTableauCNF_NTM N y ty
  let sx := encodeCNFSpinePrefix (Fx.take cend)
  let sy := encodeCNFSpinePrefix (Fy.take cend)
  apply Hsep sx sy
  apply unequal_clausePrefixes_give_unequal_spines
  exact sourceMismatch_forces_clausePrefix_difference
    M x y j hLen hClock hHead hPrev hDiff hRadius

#print axioms MCore.Real.PNPDiscovery.unequal_clausePrefixes_give_unequal_spines
#print axioms MCore.Real.PNPDiscovery.unequalBitstringsSeparate_closes_sourceEncoding

end PNPDiscovery
end Real
end MCore
