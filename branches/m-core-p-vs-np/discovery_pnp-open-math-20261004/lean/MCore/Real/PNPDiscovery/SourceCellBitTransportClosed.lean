import MCore.Real.PNPDiscovery.SourceCellBitTransport
import MCore.Real.SourceRecovery

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding
open SourceRecovery

/-- Reading inside the left side of an append is unaffected by the suffix. -/
theorem getD_append_left_bool
    (a b : BitString)
    (q : Nat)
    (hq : q < a.length) :
    (a ++ b).getD q false = a.getD q false := by
  induction a generalizing q with
  | nil =>
      simp at hq
  | cons x xs ih =>
      cases q with
      | zero =>
          simp
      | succ q =>
          have hq' : q < xs.length := by
            simpa using hq
          simpa [List.getD_cons_succ] using ih b q hq'

/-- The full tableau CNF slice at an in-range source cell is exactly its
three-clause source block. -/
theorem boundedExec_sourceCell_slice
    (M : PolyNTMCandidate)
    (x : BitString)
    (t j : Nat)
    (hj : j < ntmRadius x t) :
    symbolBlockAt
        (boundedExecTableauCNF_NTM M x t)
        (sourceCellClauseOffset M x t j) =
      initialRightCellBlock M x t j := by
  unfold boundedExecTableauCNF_NTM
  have hfit :
      sourceCellClauseOffset M x t j + 3 ≤
        (ntmInitialCNF M x t).length := by
    simpa [sourceCellClauseOffset] using
      right_slice_fits_initial M x t j hj
  rw [symbolBlockAt_append_left
    (ntmInitialCNF M x t)
    (ntmTransitionsCNF M x t ++ ntmFinalAcceptanceCNF M t)
    (sourceCellClauseOffset M x t j)
    hfit]
  exact sourceCell_clause_slice M x t j hj

/-- Exact global encoding decomposition around one source cell:
common prefix, encoded cell block, remaining tableau suffix. -/
theorem encode_tableau_split_sourceCell
    (M : PolyNTMCandidate)
    (x : BitString)
    (t j : Nat)
    (hj : j < ntmRadius x t) :
    ∃ prefix suffix : BitString,
      prefix.length = sourceCellBitOffset M x t j ∧
      prefix = encodeCNFSpinePrefix
        ((boundedExecTableauCNF_NTM M x t).take
          (sourceCellClauseOffset M x t j)) ∧
      encodeCircuit
          (ntmCNFCircuit (boundedExecTableauCNF_NTM M x t)) =
        prefix ++
          encodedSymbolBlock
            (ntmRightVar M x t 0 j)
            (sourceRightSymbol x j) ++
          suffix := by
  let F := boundedExecTableauCNF_NTM M x t
  let cstart := sourceCellClauseOffset M x t j
  let prefix := encodeCNFSpinePrefix (F.take cstart)
  let tail := F.drop cstart
  have hslice :
      tail.take 3 =
        initialRightCellBlock M x t j := by
    simpa [tail, F, symbolBlockAt] using
      boundedExec_sourceCell_slice M x t j hj
  have henc1 :=
    encode_ntmCNFCircuit_split_at F cstart
  have henc2 :=
    encode_ntmCNFCircuit_split_at tail 3
  refine ⟨prefix,
    encodeCircuit (ntmCNFCircuit (tail.drop 3)),
    ?_, rfl, ?_⟩
  · unfold prefix F cstart sourceCellBitOffset clauseBitOffset
    have htake :
        (boundedExecTableauCNF_NTM M x t).take
            (sourceCellClauseOffset M x t j) =
          (ntmInitialCNF M x t).take
            (sourceCellClauseOffset M x t j) := by
      unfold boundedExecTableauCNF_NTM
      have hle :
          sourceCellClauseOffset M x t j ≤
            (ntmInitialCNF M x t).length := by
        have hfit :=
          right_slice_fits_initial M x t j hj
        omega
      rw [List.take_append_of_le hle]
    rw [htake]
  · rw [henc1]
    change
      prefix ++ encodeCircuit (ntmCNFCircuit tail) =
        prefix ++
          encodedSymbolBlock
            (ntmRightVar M x t 0 j)
            (sourceRightSymbol x j) ++
          encodeCircuit (ntmCNFCircuit (tail.drop 3))
    rw [henc2]
    rw [hslice]
    unfold initialRightCellBlock ntmSetRightCell
    unfold encodedSymbolBlock
    simp [List.append_assoc]

/-- The final mechanical source-cell bit transport is CLOSED. -/
theorem sourceCellBitTransport_closed :
    SourceCellBitTransportGap := by
  intro M x y W
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  let Fx := boundedExecTableauCNF_NTM N x tx
  let Fy := boundedExecTableauCNF_NTM N y ty
  have hClock : tx = ty := W.clock_eq
  have hjx : W.j < ntmRadius x tx := by
    omega
  have hjy : W.j < ntmRadius y ty := by
    simpa [ntmRadius, W.length_eq, W.clock_eq] using hjx
  rcases encode_tableau_split_sourceCell N x tx W.j hjx with
    ⟨px, sx, hpxLen, hpx, hxEnc⟩
  rcases encode_tableau_split_sourceCell N y ty W.j hjy with
    ⟨py, sy, hpyLen, hpy, hyEnc⟩
  have hPrefixClauses :
      Fx.take (sourceCellClauseOffset N x tx W.j) =
        Fy.take (sourceCellClauseOffset N y ty W.j) := by
    have A : SourcePrefixLayoutAlignment M x y W.j :=
      { length_eq := W.length_eq
        clock_eq := W.clock_eq
        head_eq := W.head_eq
        source_eq := W.prefix_eq
        within_radius := by omega }
    have hx :=
      boundedExec_take_sourcePrefix N x tx W.j (by omega)
    have hy :=
      boundedExec_take_sourcePrefix N y ty W.j (by
        simpa [ntmRadius, W.length_eq, W.clock_eq] using
          (show W.j ≤ ntmRadius x tx by omega))
    have hp := sourcePrefixClauses_eq M x y W.j A
    simpa [Fx, Fy, sourcePrefixClauseEnd] using
      (hx.trans (hp.trans hy.symm))
  have hPrefixBits : px = py := by
    rw [hpx, hpy]
    have hcstart :
        sourceCellClauseOffset N x tx W.j =
          sourceCellClauseOffset N y ty W.j := by
      unfold sourceCellClauseOffset
      simp [rightBlockOffset, W.length_eq, W.clock_eq]
    rw [hcstart] at hPrefixClauses
    exact congrArg encodeCNFSpinePrefix hPrefixClauses
  have hStart :
      sourceCellBitOffset N x tx W.j =
        sourceCellBitOffset N y ty W.j := by
    rw [← hpxLen, ← hpyLen, hPrefixBits]
  have hvar :
      ntmRightVar N x tx 0 W.j =
        ntmRightVar N y ty 0 W.j := by
    subst ty
    funext a
    exact ntmRightVar_eq_of_length_eq N a W.length_eq
  have hlocal :=
    encodedSymbolBlock_target_mismatch_bit
      (ntmRightVar N x tx 0 W.j)
      (sourceRightSymbol x W.j)
      (sourceRightSymbol y W.j)
      W.source_diff
  rcases hlocal with ⟨ql, hql, hldiff⟩
  let q := sourceCellBitOffset N x tx W.j + ql
  refine ⟨q, hStart, ?_, ?_, ?_⟩
  · simp [q, hStart]
  · have hEx :
        sourcePrefixBitEnd N x tx (W.j + 1) =
          sourceCellBitOffset N x tx W.j +
            (encodedSymbolBlock
              (ntmRightVar N x tx 0 W.j)
              (sourceRightSymbol x W.j)).length := by
      have hnum :=
        sourceMismatch_globalBit M x y W
      rcases hnum with ⟨q0, hb, hs, he⟩
      have hSucc :=
        sourcePrefixClauses_succ N x tx W.j (by omega)
      unfold sourcePrefixBitEnd tableauClauseBitOffset clauseBitOffset
      rw [boundedExec_take_sourcePrefix N x tx (W.j + 1) (by omega)]
      rw [hSucc, encodeCNFSpinePrefix_append]
      rw [sourceCellBitOffset_eq_prefix_length N x tx W.j (by omega)]
      rfl
    have hEy :
        sourcePrefixBitEnd N y ty (W.j + 1) =
          sourceCellBitOffset N y ty W.j +
            (encodedSymbolBlock
              (ntmRightVar N y ty 0 W.j)
              (sourceRightSymbol y W.j)).length := by
      have hSucc :=
        sourcePrefixClauses_succ N y ty W.j (by omega)
      unfold sourcePrefixBitEnd tableauClauseBitOffset clauseBitOffset
      rw [boundedExec_take_sourcePrefix N y ty (W.j + 1) (by omega)]
      rw [hSucc, encodeCNFSpinePrefix_append]
      rw [sourceCellBitOffset_eq_prefix_length N y ty W.j (by omega)]
      rfl
    have hBlockLen :
        (encodedSymbolBlock
          (ntmRightVar N x tx 0 W.j)
          (sourceRightSymbol x W.j)).length =
        (encodedSymbolBlock
          (ntmRightVar N y ty 0 W.j)
          (sourceRightSymbol y W.j)).length := by
      rw [hvar]
      exact encodedSymbolBlock_length_target_independent _ _ _
    rw [hEx, hEy, hStart, hBlockLen]
    simp [q]
    exact hql
  · rw [hxEnc, hyEnc, hPrefixBits, hvar]
    have hLeftX :
        (px ++
          encodedSymbolBlock
            (ntmRightVar N x tx 0 W.j)
            (sourceRightSymbol x W.j) ++ sx).getD q false =
          (encodedSymbolBlock
            (ntmRightVar N x tx 0 W.j)
            (sourceRightSymbol x W.j)).getD ql false := by
      rw [getD_append_right_bool px
        (encodedSymbolBlock
          (ntmRightVar N x tx 0 W.j)
          (sourceRightSymbol x W.j) ++ sx)
        ql]
      · apply getD_append_left_bool
        exact hql
      · simp [q, hpxLen]
        exact hql
    have hLeftY :
        (px ++
          encodedSymbolBlock
            (ntmRightVar N x tx 0 W.j)
            (sourceRightSymbol y W.j) ++ sy).getD q false =
          (encodedSymbolBlock
            (ntmRightVar N x tx 0 W.j)
            (sourceRightSymbol y W.j)).getD ql false := by
      rw [getD_append_right_bool px
        (encodedSymbolBlock
          (ntmRightVar N x tx 0 W.j)
          (sourceRightSymbol y W.j) ++ sy)
        ql]
      · apply getD_append_left_bool
        have hlen :=
          encodedSymbolBlock_length_target_independent
            (ntmRightVar N x tx 0 W.j)
            (sourceRightSymbol x W.j)
            (sourceRightSymbol y W.j)
        simpa [hlen] using hql
      · simp [q, hpxLen]
        exact hql
    rw [hLeftX, hLeftY]
    exact hldiff

/-- Thus the earlier localization gap is also CLOSED. -/
theorem sourceCellMismatchLocalization_closed :
    SourceCellMismatchLocalizationGap :=
  sourceCellBitTransport_closes_localization
    sourceCellBitTransport_closed

#print axioms MCore.Real.PNPDiscovery.getD_append_left_bool
#print axioms MCore.Real.PNPDiscovery.boundedExec_sourceCell_slice
#print axioms MCore.Real.PNPDiscovery.encode_tableau_split_sourceCell
#print axioms MCore.Real.PNPDiscovery.sourceCellBitTransport_closed
#print axioms MCore.Real.PNPDiscovery.sourceCellMismatchLocalization_closed

end PNPDiscovery
end Real
end MCore
