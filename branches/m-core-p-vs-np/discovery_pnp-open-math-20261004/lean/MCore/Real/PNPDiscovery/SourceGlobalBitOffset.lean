import MCore.Real.PNPDiscovery.SymbolBlockLocalization

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding
open SourceRecovery

/-- The CNF spine encoder distributes exactly over append. -/
theorem encodeCNFSpinePrefix_append
    (F G : NTMCNF) :
    encodeCNFSpinePrefix (F ++ G) =
      encodeCNFSpinePrefix F ++
        encodeCNFSpinePrefix G := by
  induction F with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [encodeCNFSpinePrefix, ih, List.append_assoc]

/-- At an in-range source-cell boundary, the next source prefix is exactly
the previous source prefix followed by that cell's three-clause block. -/
theorem sourcePrefixClauses_succ
    (M : PolyNTMCandidate)
    (x : BitString)
    (t j : Nat)
    (hj : j + 1 ≤ ntmRadius x t) :
    sourcePrefixClauses M x t (j + 1) =
      sourcePrefixClauses M x t j ++
        initialRightCellBlock M x t j := by
  unfold sourcePrefixClauses firstKRightBlocks
  rw [List.range_succ]
  simp [List.flatMap_append, List.append_assoc]

/-- The bit offset of source cell j is exactly the encoded length of the
canonical clause prefix before that cell. -/
theorem sourceCellBitOffset_eq_prefix_length
    (M : PolyNTMCandidate)
    (x : BitString)
    (t j : Nat)
    (hj : j ≤ ntmRadius x t) :
    sourceCellBitOffset M x t j =
      (encodeCNFSpinePrefix
        (sourcePrefixClauses M x t j)).length := by
  unfold sourceCellBitOffset clauseBitOffset sourceCellClauseOffset
  have htake :
      (ntmInitialCNF M x t).take
          (rightBlockOffset M x.length t + 3 * j) =
        sourcePrefixClauses M x t j := by
    have hfull :=
      boundedExec_take_sourcePrefix M x t j hj
    unfold boundedExecTableauCNF_NTM at hfull
    have hlen :
        sourcePrefixClauseEnd M x t j ≤
          (ntmInitialCNF M x t).length := by
      rw [← rightClauseEnd_eq_initial_length]
      unfold sourcePrefixClauseEnd rightClauseEnd
      omega
    have hinit :
        (ntmInitialCNF M x t ++
          ntmTransitionsCNF M x t ++
          ntmFinalAcceptanceCNF M t).take
            (sourcePrefixClauseEnd M x t j) =
          (ntmInitialCNF M x t).take
            (sourcePrefixClauseEnd M x t j) := by
      rw [List.take_append_of_le hlen]
    rw [hinit] at hfull
    simpa [sourcePrefixClauseEnd] using hfull
  rw [htake]

/-- Generic getD transport into the right-hand side of an append. -/
theorem getD_append_right_bool
    (a b : BitString)
    (q : Nat)
    (hq : q < b.length) :
    (a ++ b).getD (a.length + q) false =
      b.getD q false := by
  induction a with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.getD_cons_succ, ih, Nat.add_assoc]

/-- A source-symbol mismatch is localized to a concrete global bit inside the
encoded source-cell block. -/
theorem sourceMismatch_globalBit
    (M : PolyDTMCandidate)
    (x y : BitString)
    (W : SourceMismatchWitness M x y) :
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    let bx := sourceCellBitOffset N x tx W.j
    let by := sourceCellBitOffset N y ty W.j
    let ex := sourcePrefixBitEnd N x tx (W.j + 1)
    let ey := sourcePrefixBitEnd N y ty (W.j + 1)
    ∃ q : Nat,
      bx = by ∧
      Nat.min bx by ≤ q ∧
      q < Nat.min ex ey := by
  dsimp
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  have hClock : tx = ty := W.clock_eq
  have hRadiusX :
      W.j + 1 ≤ ntmRadius x tx := W.in_radius
  have hRadiusY :
      W.j + 1 ≤ ntmRadius y ty := by
    simpa [ntmRadius, W.length_eq, W.clock_eq] using hRadiusX
  have hPrefixJ :
      sourcePrefixClauses N x tx W.j =
        sourcePrefixClauses N y ty W.j := by
    let A : SourcePrefixLayoutAlignment M x y W.j :=
      { length_eq := W.length_eq
        clock_eq := W.clock_eq
        head_eq := W.head_eq
        source_eq := W.prefix_eq
        within_radius := by omega }
    exact sourcePrefixClauses_eq M x y W.j A
  have hbx :
      sourceCellBitOffset N x tx W.j =
        (encodeCNFSpinePrefix
          (sourcePrefixClauses N x tx W.j)).length :=
    sourceCellBitOffset_eq_prefix_length N x tx W.j (by omega)
  have hby :
      sourceCellBitOffset N y ty W.j =
        (encodeCNFSpinePrefix
          (sourcePrefixClauses N y ty W.j)).length :=
    sourceCellBitOffset_eq_prefix_length N y ty W.j (by omega)
  have hbEq :
      sourceCellBitOffset N x tx W.j =
        sourceCellBitOffset N y ty W.j := by
    rw [hbx, hby, hPrefixJ]
  let vx := ntmRightVar N x tx 0 W.j
  have hlocal :=
    sourceCell_target_mismatch_localBit
      N x y tx W.j W.length_eq W.source_diff
  rcases hlocal with ⟨ql, hql, hldiff⟩
  refine ⟨sourceCellBitOffset N x tx W.j + ql, hbEq, ?_, ?_⟩
  · simp [hbEq]
  · have hSuccX :
      sourcePrefixClauses N x tx (W.j + 1) =
        sourcePrefixClauses N x tx W.j ++
          initialRightCellBlock N x tx W.j :=
      sourcePrefixClauses_succ N x tx W.j hRadiusX
    have hSuccY :
      sourcePrefixClauses N y ty (W.j + 1) =
        sourcePrefixClauses N y ty W.j ++
          initialRightCellBlock N y ty W.j :=
      sourcePrefixClauses_succ N y ty W.j hRadiusY
    have hEx :
        sourcePrefixBitEnd N x tx (W.j + 1) =
          sourceCellBitOffset N x tx W.j +
            (encodedSymbolBlock
              (ntmRightVar N x tx 0 W.j)
              (sourceRightSymbol x W.j)).length := by
      unfold sourcePrefixBitEnd tableauClauseBitOffset clauseBitOffset
      rw [boundedExec_take_sourcePrefix N x tx (W.j + 1) hRadiusX]
      rw [hSuccX, encodeCNFSpinePrefix_append]
      rw [sourceCellBitOffset_eq_prefix_length N x tx W.j (by omega)]
      rfl
    have hEy :
        sourcePrefixBitEnd N y ty (W.j + 1) =
          sourceCellBitOffset N y ty W.j +
            (encodedSymbolBlock
              (ntmRightVar N y ty 0 W.j)
              (sourceRightSymbol y W.j)).length := by
      unfold sourcePrefixBitEnd tableauClauseBitOffset clauseBitOffset
      rw [boundedExec_take_sourcePrefix N y ty (W.j + 1) hRadiusY]
      rw [hSuccY, encodeCNFSpinePrefix_append]
      rw [sourceCellBitOffset_eq_prefix_length N y ty W.j (by omega)]
      rfl
    have hvar :
        ntmRightVar N x tx 0 W.j =
          ntmRightVar N y ty 0 W.j := by
      subst ty
      funext a
      exact ntmRightVar_eq_of_length_eq N a W.length_eq
    have hblockLen :
        (encodedSymbolBlock
          (ntmRightVar N x tx 0 W.j)
          (sourceRightSymbol x W.j)).length =
        (encodedSymbolBlock
          (ntmRightVar N y ty 0 W.j)
          (sourceRightSymbol y W.j)).length := by
      rw [hvar]
      exact encodedSymbolBlock_length_target_independent _ _ _
    rw [hEx, hEy, hbEq, hblockLen]
    simp
    exact hql

/-- The numeric localization part of SourceCellMismatchLocalizationGap is now
closed: every source mismatch lies between its cell-start and cell-end
boundaries. -/
def SourceCellNumericLocalization : Prop :=
  ∀ (M : PolyDTMCandidate)
    (x y : BitString)
    (W : SourceMismatchWitness M x y),
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    let bx := sourceCellBitOffset N x tx W.j
    let by := sourceCellBitOffset N y ty W.j
    let ex := sourcePrefixBitEnd N x tx (W.j + 1)
    let ey := sourcePrefixBitEnd N y ty (W.j + 1)
    ∃ q : Nat,
      bx = by ∧
      Nat.min bx by ≤ q ∧
      q < Nat.min ex ey

theorem sourceCellNumericLocalization_closed :
    SourceCellNumericLocalization :=
  sourceMismatch_globalBit

#print axioms MCore.Real.PNPDiscovery.encodeCNFSpinePrefix_append
#print axioms MCore.Real.PNPDiscovery.sourceCellBitOffset_eq_prefix_length
#print axioms MCore.Real.PNPDiscovery.getD_append_right_bool
#print axioms MCore.Real.PNPDiscovery.sourceMismatch_globalBit
#print axioms MCore.Real.PNPDiscovery.sourceCellNumericLocalization_closed

end PNPDiscovery
end Real
end MCore
