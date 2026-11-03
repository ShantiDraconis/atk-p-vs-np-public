import MCore.Real.PNPDiscovery.HeadParityPressure
import MCore.Real.PNPDiscovery.SourcePrefixCoverageClosed

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding
open SourceRecovery

/-- Canonical circuit encoding is injective because decodeCircuit is a left
inverse on the entire image. -/
theorem encodeCircuit_injective :
    Function.Injective encodeCircuit := by
  intro a b h
  have ha := decodeCircuit_encode a
  have hb := decodeCircuit_encode b
  rw [h] at ha
  rw [hb] at ha
  exact Option.some.inj ha

/-- CNF-to-circuit encoding is injective on concrete NTMCNF values. -/
theorem ntmCNFCircuit_injective :
    Function.Injective ntmCNFCircuit := by
  intro F G h
  have hF := decodeNTMCNF_ntmCNFCircuit F
  have hG := decodeNTMCNF_ntmCNFCircuit G
  rw [h] at hF
  rw [hG] at hF
  exact Option.some.inj hF

/-- Hence complete canonical bit encodings of concrete NTMCNFs are injective. -/
theorem encode_ntmCNFCircuit_injective :
    Function.Injective
      (fun F : NTMCNF => encodeCircuit (ntmCNFCircuit F)) := by
  intro F G h
  apply ntmCNFCircuit_injective
  exact encodeCircuit_injective h

/-- A source-symbol mismatch at cell j forces the concrete clause prefix
through cell j to differ, provided all earlier layout parameters align. -/
theorem sourceMismatch_forces_clausePrefix_difference
    (M : PolyDTMCandidate)
    (x y : BitString)
    (j : Nat)
    (hLen : x.length = y.length)
    (hClock :
      M.timeBound x.length = M.timeBound y.length)
    (hHead :
      sourceHeadSymbol x = sourceHeadSymbol y)
    (hPrev :
      SourceRightPrefixAligned x y j)
    (hDiff :
      sourceRightSymbol x j ≠ sourceRightSymbol y j)
    (hRadius :
      j + 1 ≤ ntmRadius x (M.timeBound x.length)) :
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    let cend := sourcePrefixClauseEnd N x tx (j + 1)
    (boundedExecTableauCNF_NTM N x tx).take cend ≠
      (boundedExecTableauCNF_NTM N y ty).take cend := by
  dsimp
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  have hRadiusY :
      j + 1 ≤ ntmRadius y ty := by
    simpa [ntmRadius, hLen, hClock] using hRadius
  have hPrefixX :=
    boundedExec_take_sourcePrefix N x tx (j + 1) hRadius
  have hPrefixY :=
    boundedExec_take_sourcePrefix N y ty (j + 1) hRadiusY
  rw [hPrefixX, hPrefixY]
  intro hEq
  have hState :
      ntmSetStateClauses [] N tx 0 N.machine.initial =
        ntmSetStateClauses [] N ty 0 N.machine.initial := by
    rw [hClock]
  have hHeadBlock :
      initialHeadBlock N x tx =
        initialHeadBlock N y ty := by
    exact initialHeadBlock_eq_of_clock_head
      N x y tx ty hClock hHead
  have hLeft :
      initialLeftBlock N x tx =
        initialLeftBlock N y ty := by
    exact initialLeftBlock_eq_of_length_clock
      N x y tx ty hLen hClock
  have hCellDiff :
      initialRightCellBlock N x tx j ≠
        initialRightCellBlock N y ty j := by
    intro hCellEq
    have hSym :
        sourceRightSymbol x j =
          sourceRightSymbol y j := by
      have hClock' : tx = ty := hClock
      subst ty
      exact rightCellBlockInjectivity_closed
        N x y tx j hLen hCellEq
    exact hDiff hSym
  have hFirstJ :
      firstKRightBlocks N x tx j =
        firstKRightBlocks N y ty j := by
    rw [← hClock]
    exact firstKRightBlocks_eq N x y tx j hLen hPrev
  unfold sourcePrefixClauses at hEq
  rw [hState, hHeadBlock, hLeft, hFirstJ] at hEq
  simp [firstKRightBlocks, List.range_succ] at hEq
  exact hCellDiff hEq

/-- New encoding-localization frontier exposed by the previous theorem.
The two clause prefixes are different, but their encoded lengths need not be
definitionally equal because literal variable IDs are unary-encoded.  To make
the mismatch visible to the shared read cone we must either prove equal
encoded boundary lengths or exhibit a differing bit before the smaller
boundary. -/
def SourceMismatchBitLocalizationGap : Prop :=
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
    let cend := sourcePrefixClauseEnd N x tx (j + 1)
    let Fx := boundedExecTableauCNF_NTM N x tx
    let Fy := boundedExecTableauCNF_NTM N y (M.timeBound y.length)
    let bx := clauseBitOffset Fx cend
    let by := clauseBitOffset Fy cend
    ∃ q : Nat,
      q < Nat.min bx by ∧
      (encodeCircuit (ntmCNFCircuit Fx)).getD q false ≠
        (encodeCircuit (ntmCNFCircuit Fy)).getD q false

/-- We have already reduced this frontier to unequal concrete clause prefixes. -/
theorem sourceMismatch_clause_frontier
    (M : PolyDTMCandidate)
    (x y : BitString)
    (j : Nat)
    (hLen : x.length = y.length)
    (hClock :
      M.timeBound x.length = M.timeBound y.length)
    (hHead :
      sourceHeadSymbol x = sourceHeadSymbol y)
    (hPrev :
      SourceRightPrefixAligned x y j)
    (hDiff :
      sourceRightSymbol x j ≠ sourceRightSymbol y j)
    (hRadius :
      j + 1 ≤ ntmRadius x (M.timeBound x.length)) :
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    let cend := sourcePrefixClauseEnd N x tx (j + 1)
    (boundedExecTableauCNF_NTM N x tx).take cend ≠
      (boundedExecTableauCNF_NTM N y ty).take cend :=
  sourceMismatch_forces_clausePrefix_difference
    M x y j hLen hClock hHead hPrev hDiff hRadius

#print axioms MCore.Real.PNPDiscovery.encodeCircuit_injective
#print axioms MCore.Real.PNPDiscovery.ntmCNFCircuit_injective
#print axioms MCore.Real.PNPDiscovery.sourceMismatch_forces_clausePrefix_difference
#print axioms MCore.Real.PNPDiscovery.sourceMismatch_clause_frontier

end PNPDiscovery
end Real
end MCore
