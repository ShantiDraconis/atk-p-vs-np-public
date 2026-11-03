import MCore.Real.PNPDiscovery.SourceBitOffsets
import MCore.Real.SourceRecovery

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding
open SourceRecovery

/-- Canonical clause-level regions of a bounded Cook--Levin tableau. -/
inductive TableauClauseRegion
  | state
  | head
  | left
  | right
  | transitions
  | finalAcceptance
  | pastEnd
  deriving Repr, DecidableEq

def stateClauseEnd
    (M : PolyNTMCandidate) : Nat :=
  initialStateClauseCount M

def headClauseEnd
    (M : PolyNTMCandidate) : Nat :=
  stateClauseEnd M + 3

def leftClauseEnd
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Nat :=
  rightBlockOffset M x.length t

def rightClauseEnd
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Nat :=
  rightBlockOffset M x.length t +
    3 * ntmRadius x t

def transitionClauseEnd
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Nat :=
  (ntmInitialCNF M x t).length +
    (ntmTransitionsCNF M x t).length

def tableauClauseEnd
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Nat :=
  (boundedExecTableauCNF_NTM M x t).length

/-- The initial CNF ends exactly after the right-tape block. -/
theorem rightClauseEnd_eq_initial_length
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    rightClauseEnd M x t =
      (ntmInitialCNF M x t).length := by
  simp [rightClauseEnd, ntmInitialCNF,
    rightBlockOffset, initialStateClauseCount,
    retainedRadius, ntmRadius, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

/-- Transition block ends exactly where the final-acceptance block begins. -/
theorem transitionClauseEnd_eq_prefix_length
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    transitionClauseEnd M x t =
      (ntmInitialCNF M x t ++
        ntmTransitionsCNF M x t).length := by
  simp [transitionClauseEnd]

/-- Full tableau length decomposes into initial, transition and final blocks. -/
theorem tableauClauseEnd_decomposition
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    tableauClauseEnd M x t =
      transitionClauseEnd M x t +
        (ntmFinalAcceptanceCNF M t).length := by
  simp [tableauClauseEnd, boundedExecTableauCNF_NTM,
    transitionClauseEnd, Nat.add_assoc]

/-- Pure arithmetic classifier for one clause index. -/
def classifyClause
    (M : PolyNTMCandidate)
    (x : BitString)
    (t j : Nat) : TableauClauseRegion :=
  if j < stateClauseEnd M then
    .state
  else if j < headClauseEnd M then
    .head
  else if j < leftClauseEnd M x t then
    .left
  else if j < rightClauseEnd M x t then
    .right
  else if j < transitionClauseEnd M x t then
    .transitions
  else if j < tableauClauseEnd M x t then
    .finalAcceptance
  else
    .pastEnd

/-- Every in-range source/right cell is classified literally as RIGHT. -/
theorem classify_sourceCellClause_right
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t) :
    classifyClause M x t
      (sourceCellClauseOffset M x t i) =
        .right := by
  unfold classifyClause sourceCellClauseOffset
  have hState :
      ¬ rightBlockOffset M x.length t + 3 * i <
          stateClauseEnd M := by
    simp [rightBlockOffset, stateClauseEnd,
      initialStateClauseCount, retainedRadius]
  have hHead :
      ¬ rightBlockOffset M x.length t + 3 * i <
          headClauseEnd M := by
    simp [rightBlockOffset, headClauseEnd, stateClauseEnd,
      initialStateClauseCount, retainedRadius]
  have hLeft :
      ¬ rightBlockOffset M x.length t + 3 * i <
          leftClauseEnd M x t := by
    simp [leftClauseEnd]
  have hRight :
      rightBlockOffset M x.length t + 3 * i <
        rightClauseEnd M x t := by
    unfold rightClauseEnd
    omega
  simp [hState, hHead, hLeft, hRight]

/-- The region boundaries are monotonically ordered. -/
theorem region_boundary_order
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    stateClauseEnd M ≤
      headClauseEnd M ∧
    headClauseEnd M ≤
      leftClauseEnd M x t ∧
    leftClauseEnd M x t ≤
      rightClauseEnd M x t ∧
    rightClauseEnd M x t ≤
      transitionClauseEnd M x t ∧
    transitionClauseEnd M x t ≤
      tableauClauseEnd M x t := by
  constructor
  · simp [stateClauseEnd, headClauseEnd]
  constructor
  · simp [headClauseEnd, leftClauseEnd, rightBlockOffset,
      stateClauseEnd, initialStateClauseCount, retainedRadius,
      ntmRadius]
  constructor
  · simp [leftClauseEnd, rightClauseEnd]
  constructor
  · rw [rightClauseEnd_eq_initial_length]
    simp [transitionClauseEnd]
  · simp [tableauClauseEnd, boundedExecTableauCNF_NTM,
      transitionClauseEnd]

/-- Clause-level classification is total by construction. -/
theorem classifyClause_cases
    (M : PolyNTMCandidate)
    (x : BitString)
    (t j : Nat) :
    classifyClause M x t j = .state ∨
    classifyClause M x t j = .head ∨
    classifyClause M x t j = .left ∨
    classifyClause M x t j = .right ∨
    classifyClause M x t j = .transitions ∨
    classifyClause M x t j = .finalAcceptance ∨
    classifyClause M x t j = .pastEnd := by
  unfold classifyClause
  split <;> split <;> split <;> split <;> split <;> split <;>
    simp_all

#print axioms MCore.Real.PNPDiscovery.rightClauseEnd_eq_initial_length
#print axioms MCore.Real.PNPDiscovery.classify_sourceCellClause_right
#print axioms MCore.Real.PNPDiscovery.region_boundary_order
#print axioms MCore.Real.PNPDiscovery.classifyClause_cases

end PNPDiscovery
end Real
end MCore
