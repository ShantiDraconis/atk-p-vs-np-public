import MCore.Real.PNPDiscovery.SourcePrefixPressure

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding

/-- Generic encoder transport: equality of the first k CNF clauses implies
equality of the encoded bit prefixes ending exactly at that clause boundary. -/
theorem encode_prefix_of_clause_prefix_eq
    (F G : NTMCNF)
    (k : Nat)
    (hFG : F.take k = G.take k) :
    let b := clauseBitOffset F k
    b = clauseBitOffset G k ∧
      (encodeCircuit (ntmCNFCircuit F)).take b =
        (encodeCircuit (ntmCNFCircuit G)).take b := by
  dsimp
  have hb :
      clauseBitOffset F k = clauseBitOffset G k := by
    unfold clauseBitOffset
    rw [hFG]
  constructor
  · exact hb
  · rw [take_clauseBitOffset F k]
    rw [hb]
    rw [take_clauseBitOffset G k]
    rw [hFG]

/-- The only remaining list/layout bridge needed for source-prefix coverage:
under literal alignment, the two concrete tableaux have identical clause
prefixes through the first k source/right cells. -/
def SourcePrefixClauseCoverageGap : Prop :=
  ∀ (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (k : Nat)
    (A : SourcePrefixLayoutAlignment M x y k),
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    let cend := sourcePrefixClauseEnd N x tx k
    (boundedExecTableauCNF_NTM N x tx).take cend =
      (boundedExecTableauCNF_NTM N y ty).take cend

/-- Once clause-level coverage is available, encoded bit coverage follows
mechanically. -/
theorem sourcePrefixClauseCoverage_to_bitCoverage
    (H : SourcePrefixClauseCoverageGap) :
    SourcePrefixCoverageGap := by
  intro M hTotal x y k A
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  let cend := sourcePrefixClauseEnd N x tx k
  let Fx := boundedExecTableauCNF_NTM N x tx
  let Fy := boundedExecTableauCNF_NTM N y ty
  have hClauses : Fx.take cend = Fy.take cend := by
    exact H M hTotal x y k A
  have hEnc :=
    encode_prefix_of_clause_prefix_eq Fx Fy cend hClauses
  have hClock : tx = ty := by
    exact A.clock_eq
  have hLen : x.length = y.length := A.length_eq
  unfold R_M complementSemanticReduction
  simp only [PNPNTMTableauClosure.concreteNTMTableauProducer,
    PNPNTMTableauClosure.ntmTableauProducerOfCertificates,
    complementRunRealization, complementToNTMCandidate]
  change
    (encodeCircuit (ntmCNFCircuit Fx)).take
        (sourcePrefixBitEnd N x tx k) =
      (encodeCircuit (ntmCNFCircuit Fy)).take
        (sourcePrefixBitEnd N x tx k)
  unfold sourcePrefixBitEnd tableauClauseBitOffset
  change
    (encodeCircuit (ntmCNFCircuit Fx)).take
        (clauseBitOffset Fx cend) =
      (encodeCircuit (ntmCNFCircuit Fy)).take
        (clauseBitOffset Fx cend)
  exact hEnc.2

/-- The bit-level OPEN bridge is therefore no stronger than the single
clause-prefix equality above. -/
theorem sourcePrefixCoverage_reduced_to_clauseCoverage :
    SourcePrefixClauseCoverageGap →
      SourcePrefixCoverageGap :=
  sourcePrefixClauseCoverage_to_bitCoverage

#print axioms MCore.Real.PNPDiscovery.encode_prefix_of_clause_prefix_eq
#print axioms MCore.Real.PNPDiscovery.sourcePrefixClauseCoverage_to_bitCoverage

end PNPDiscovery
end Real
end MCore
