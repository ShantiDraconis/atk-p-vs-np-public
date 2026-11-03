import MCore.Real.PNPDiscovery.SourcePrefixEncoderBridge

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding
open SourceRecovery

/-- Generic prefix decomposition for flatMap over List.range. -/
theorem flatMap_range_prefix_exists
    {α : Type}
    (f : Nat → List α)
    (k n : Nat)
    (hkn : k ≤ n) :
    ∃ tail : List α,
      (List.range n).flatMap f =
        (List.range k).flatMap f ++ tail := by
  induction n with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      exact ⟨[], by simp⟩
  | succ n ih =>
      by_cases hk : k ≤ n
      · rcases ih hk with ⟨tail, htail⟩
        refine ⟨tail ++ f n, ?_⟩
        rw [List.range_succ, List.flatMap_append]
        simp only [List.flatMap_singleton]
        rw [htail]
        simp [List.append_assoc]
      · have hkeq : k = n + 1 := by omega
        subst k
        exact ⟨[], by simp⟩

/-- Therefore a flatMap over the first k indices is literally a prefix of the
same flatMap over any larger range. -/
theorem flatMap_range_prefix_take
    {α : Type}
    (f : Nat → List α)
    (k n : Nat)
    (hkn : k ≤ n) :
    ((List.range n).flatMap f).take
        ((List.range k).flatMap f).length =
      (List.range k).flatMap f := by
  rcases flatMap_range_prefix_exists f k n hkn with
    ⟨tail, h⟩
  rw [h]
  simp

/-- Every encoded right/source cell contributes exactly three CNF clauses. -/
@[simp] theorem firstKRightBlocks_length
    (M : PolyNTMCandidate)
    (x : BitString)
    (t k : Nat) :
    (firstKRightBlocks M x t k).length = 3 * k := by
  simp [firstKRightBlocks, initialRightCellBlock,
    ntmSetRightCell, length_ntmSetSymbolClauses, Nat.mul_comm]

/-- The first k concrete right/source blocks are exactly the first 3*k clauses
of the full right block whenever k stays inside the retained radius. -/
theorem rightBlock_take_firstK
    (M : PolyNTMCandidate)
    (x : BitString)
    (t k : Nat)
    (hk : k ≤ ntmRadius x t) :
    ((List.range (ntmRadius x t)).flatMap
      (fun i => initialRightCellBlock M x t i)).take (3 * k) =
        firstKRightBlocks M x t k := by
  have h :=
    flatMap_range_prefix_take
      (fun i => initialRightCellBlock M x t i)
      k (ntmRadius x t) hk
  simpa [firstKRightBlocks_length] using h

/-- Canonical clause prefix through the first k right/source cells. -/
def sourcePrefixClauses
    (M : PolyNTMCandidate)
    (x : BitString)
    (t k : Nat) : NTMCNF :=
  ntmSetStateClauses [] M t 0 M.machine.initial ++
  initialHeadBlock M x t ++
  initialLeftBlock M x t ++
  firstKRightBlocks M x t k

/-- Its length is exactly the previously defined sourcePrefixClauseEnd. -/
theorem sourcePrefixClauses_length
    (M : PolyNTMCandidate)
    (x : BitString)
    (t k : Nat) :
    (sourcePrefixClauses M x t k).length =
      sourcePrefixClauseEnd M x t k := by
  unfold sourcePrefixClauses sourcePrefixClauseEnd
  rw [rightBlockOffset_eq_prefix_length M x t]
  simp [firstKRightBlocks_length, initialHeadBlock,
    initialLeftBlock, Nat.add_assoc]

/-- Taking the concrete tableau through sourcePrefixClauseEnd returns exactly
the canonical state+head+left+first-k-right prefix. -/
theorem boundedExec_take_sourcePrefix
    (M : PolyNTMCandidate)
    (x : BitString)
    (t k : Nat)
    (hk : k ≤ ntmRadius x t) :
    (boundedExecTableauCNF_NTM M x t).take
        (sourcePrefixClauseEnd M x t k) =
      sourcePrefixClauses M x t k := by
  rw [← sourcePrefixClauses_length M x t k]
  unfold boundedExecTableauCNF_NTM
  rw [ntmInitialCNF_four_blocks]
  unfold sourcePrefixClauses
  let pre :=
    ntmSetStateClauses [] M t 0 M.machine.initial ++
    initialHeadBlock M x t ++
    initialLeftBlock M x t
  let right :=
    (List.range (ntmRadius x t)).flatMap
      (fun i => initialRightCellBlock M x t i)
  have hright :
      right.take (3 * k) =
        firstKRightBlocks M x t k := by
    simpa [right] using rightBlock_take_firstK M x t k hk
  have hprelen :
      pre.length = rightBlockOffset M x.length t := by
    simpa [pre, initialHeadBlock, initialLeftBlock]
      using rightBlockOffset_eq_prefix_length M x t
  have hprefixlen :
      (pre ++ firstKRightBlocks M x t k).length =
        pre.length + 3 * k := by
    simp [firstKRightBlocks_length]
  change
    (pre ++ right ++
      ntmTransitionsCNF M x t ++
      ntmFinalAcceptanceCNF M t).take
        (pre ++ firstKRightBlocks M x t k).length =
      pre ++ firstKRightBlocks M x t k
  rw [hprefixlen]
  have hrightlen : 3 * k ≤ right.length := by
    simp [right, initialRightCellBlock, ntmSetRightCell,
      length_ntmSetSymbolClauses]
    omega
  rw [List.take_append]
  rw [List.take_append]
  simp only [List.length_append]
  rw [Nat.add_sub_cancel_left]
  rw [List.take_append_of_le hrightlen]
  rw [hright]
  simp

/-- Aligned layout makes the canonical clause prefix identical. -/
theorem sourcePrefixClauses_eq
    (M : PolyDTMCandidate)
    (x y : BitString)
    (k : Nat)
    (A : SourcePrefixLayoutAlignment M x y k) :
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    sourcePrefixClauses N x tx k =
      sourcePrefixClauses N y ty k := by
  dsimp
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  have hClock : tx = ty := A.clock_eq
  have hState :
      ntmSetStateClauses [] N tx 0 N.machine.initial =
        ntmSetStateClauses [] N ty 0 N.machine.initial := by
    rw [hClock]
  have hHead :
      initialHeadBlock N x tx =
        initialHeadBlock N y ty := by
    exact initialHeadBlock_eq_of_clock_head
      N x y tx ty hClock A.head_eq
  have hLeft :
      initialLeftBlock N x tx =
        initialLeftBlock N y ty :=
    initialLeftBlock_eq_of_length_clock
      N x y tx ty A.length_eq hClock
  have hRight :
      firstKRightBlocks N x tx k =
        firstKRightBlocks N y ty k := by
    rw [← hClock]
    exact firstKRightBlocks_eq N x y tx k
      A.length_eq A.source_eq
  unfold sourcePrefixClauses
  rw [hState, hHead, hLeft, hRight]

/-- The previously isolated clause-level OPEN bridge is fully mechanical and
closes from the concrete tableau layout. -/
theorem sourcePrefixClauseCoverage_closed :
    SourcePrefixClauseCoverageGap := by
  intro M hTotal x y k A
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  let cend := sourcePrefixClauseEnd N x tx k
  have hRadiusX :
      k ≤ ntmRadius x tx := by
    exact A.within_radius
  have hRadiusY :
      k ≤ ntmRadius y ty := by
    have hr :
        ntmRadius x tx = ntmRadius y ty := by
      simp [ntmRadius, A.length_eq, A.clock_eq]
    simpa [hr] using hRadiusX
  rw [boundedExec_take_sourcePrefix N x tx k hRadiusX]
  rw [boundedExec_take_sourcePrefix N y ty k hRadiusY]
  exact sourcePrefixClauses_eq M x y k A

/-- Hence the bit-level source-prefix coverage bridge is also CLOSED. -/
theorem sourcePrefixCoverage_closed :
    SourcePrefixCoverageGap :=
  sourcePrefixClauseCoverage_to_bitCoverage
    sourcePrefixClauseCoverage_closed

#print axioms MCore.Real.PNPDiscovery.flatMap_range_prefix_exists
#print axioms MCore.Real.PNPDiscovery.rightBlock_take_firstK
#print axioms MCore.Real.PNPDiscovery.boundedExec_take_sourcePrefix
#print axioms MCore.Real.PNPDiscovery.sourcePrefixClauseCoverage_closed
#print axioms MCore.Real.PNPDiscovery.sourcePrefixCoverage_closed

end PNPDiscovery
end Real
end MCore
