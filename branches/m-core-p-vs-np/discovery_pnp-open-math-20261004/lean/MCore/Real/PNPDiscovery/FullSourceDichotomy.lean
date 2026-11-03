import MCore.Real.PNPDiscovery.SourcePrefixPressureClosed
import MCore.Real.SourceRecovery

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding
open SourceRecovery

/-- At k = retained radius, firstKRightBlocks is the complete time-zero right
block by definition. -/
theorem firstKRightBlocks_full
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    firstKRightBlocks M x t (ntmRadius x t) =
      (List.range (ntmRadius x t)).flatMap
        (fun i => initialRightCellBlock M x t i) := by
  rfl

/-- Therefore sourcePrefixClauses at full retained radius is exactly the
complete initial CNF. -/
theorem sourcePrefixClauses_full_initial
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    sourcePrefixClauses M x t (ntmRadius x t) =
      ntmInitialCNF M x t := by
  rw [ntmInitialCNF_four_blocks]
  rfl

/-- Full source-layout alignment makes the entire initial CNF equal. -/
theorem fullSourceAlignment_initialCNF_eq
    (M : PolyDTMCandidate)
    (x y : BitString)
    (A :
      SourcePrefixLayoutAlignment M x y
        (ntmRadius x (M.timeBound x.length))) :
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    ntmInitialCNF N x tx =
      ntmInitialCNF N y ty := by
  dsimp
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  have hRadius :
      ntmRadius x tx = ntmRadius y ty := by
    simp [ntmRadius, A.length_eq, A.clock_eq]
  have hPrefix :=
    sourcePrefixClauses_eq M x y
      (ntmRadius x tx) A
  rw [sourcePrefixClauses_full_initial N x tx] at hPrefix
  have hy :
      sourcePrefixClauses N y ty (ntmRadius x tx) =
        ntmInitialCNF N y ty := by
    rw [hRadius]
    exact sourcePrefixClauses_full_initial N y ty
  rw [hy] at hPrefix
  exact hPrefix

/-- The certified source decoder then forces the original inputs themselves
to be equal. -/
theorem fullSourceAlignment_inputs_eq
    (M : PolyDTMCandidate)
    (x y : BitString)
    (A :
      SourcePrefixLayoutAlignment M x y
        (ntmRadius x (M.timeBound x.length))) :
    x = y := by
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  have hCNF :
      ntmInitialCNF N x tx =
        ntmInitialCNF N y ty :=
    fullSourceAlignment_initialCNF_eq M x y A
  have hx :
      extractInitialTape N x.length tx
        (ntmInitialCNF N x tx) = some x :=
    extractInitialTape_initialCNF N x tx
  have hy :
      extractInitialTape N y.length ty
        (ntmInitialCNF N y ty) = some y :=
    extractInitialTape_initialCNF N y ty
  have hLen : x.length = y.length := A.length_eq
  have hClock : tx = ty := A.clock_eq
  rw [hCNF] at hx
  rw [hLen, hClock] at hx
  rw [hy] at hx
  exact Option.some.inj hx

/-- In a terminal-parity-barrier regime, a positive odd-separated pair cannot
have complete source-layout alignment: that would make the two orbit points
literally equal and hence give equal terminal states. -/
theorem parityBarrier_forbids_fullSourceAlignment
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    ¬ SourcePrefixLayoutAlignment M x y
        (ntmRadius x (M.timeBound x.length)) := by
  dsimp
  intro A
  have hxy :=
    fullSourceAlignment_inputs_eq
      M
      (orbit M hTotal seed (i + 1))
      (orbit M hTotal seed ((i + 1) + (2 * d + 1)))
      A
  have hState :
      terminalState M
          (orbit M hTotal seed ((i + 1) + (2 * d + 1))) =
        terminalState M
          (orbit M hTotal seed (i + 1)) := by
    rw [hxy]
  exact Hbar seed (i + 1) d hState

/-- Explicit material disjunction forced by the barrier: every positive
odd-separated pair must break at length, clock, head, or at a concrete
right/source cell before the retained radius. -/
theorem parityBarrier_source_break_dichotomy
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (Hbar : TerminalParityBarrier M hTotal)
    (seed : BitString)
    (i d : Nat) :
    let x := orbit M hTotal seed (i + 1)
    let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
    x.length ≠ y.length ∨
    M.timeBound x.length ≠ M.timeBound y.length ∨
    sourceHeadSymbol x ≠ sourceHeadSymbol y ∨
    ∃ j : Nat,
      j < ntmRadius x (M.timeBound x.length) ∧
      sourceRightSymbol x j ≠ sourceRightSymbol y j := by
  dsimp
  classical
  let x := orbit M hTotal seed (i + 1)
  let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
  by_cases hLen : x.length = y.length
  · by_cases hClock :
      M.timeBound x.length = M.timeBound y.length
    · by_cases hHead :
        sourceHeadSymbol x = sourceHeadSymbol y
      · right
        right
        right
        by_contra hNo
        push_neg at hNo
        have hSource :
            SourceRightPrefixAligned x y
              (ntmRadius x (M.timeBound x.length)) := by
          intro j hj
          exact hNo j hj
        have A :
            SourcePrefixLayoutAlignment M x y
              (ntmRadius x (M.timeBound x.length)) :=
          { length_eq := hLen
            clock_eq := hClock
            head_eq := hHead
            source_eq := hSource
            within_radius := Nat.le_refl _ }
        exact (parityBarrier_forbids_fullSourceAlignment
          M hTotal Hbar seed i d) A
      · exact Or.inr (Or.inr (Or.inl hHead))
    · exact Or.inr (Or.inl hClock)
  · exact Or.inl hLen

#print axioms MCore.Real.PNPDiscovery.fullSourceAlignment_inputs_eq
#print axioms MCore.Real.PNPDiscovery.parityBarrier_forbids_fullSourceAlignment
#print axioms MCore.Real.PNPDiscovery.parityBarrier_source_break_dichotomy

end PNPDiscovery
end Real
end MCore
