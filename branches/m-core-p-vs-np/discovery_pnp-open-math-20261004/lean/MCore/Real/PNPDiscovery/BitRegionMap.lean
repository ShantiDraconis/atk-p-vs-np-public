import MCore.Real.PNPDiscovery.TableauRegionMap

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding
open SourceRecovery

/-- Bit offset of the first encoding bit after the first k CNF clauses. -/
def tableauClauseBitOffset
    (M : PolyNTMCandidate)
    (x : BitString)
    (t k : Nat) : Nat :=
  clauseBitOffset
    (boundedExecTableauCNF_NTM M x t) k

def stateBitEnd
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Nat :=
  tableauClauseBitOffset M x t (stateClauseEnd M)

def headBitEnd
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Nat :=
  tableauClauseBitOffset M x t (headClauseEnd M)

def leftBitEnd
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Nat :=
  tableauClauseBitOffset M x t (leftClauseEnd M x t)

def rightBitEnd
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Nat :=
  tableauClauseBitOffset M x t (rightClauseEnd M x t)

def transitionBitEnd
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Nat :=
  tableauClauseBitOffset M x t (transitionClauseEnd M x t)

def tableauBitEnd
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Nat :=
  tableauClauseBitOffset M x t (tableauClauseEnd M x t)

/-- Clause-prefix bit offsets are monotone in the clause count. -/
theorem clauseBitOffset_mono
    (F : NTMCNF)
    {j k : Nat}
    (hjk : j ≤ k) :
    clauseBitOffset F j ≤ clauseBitOffset F k := by
  unfold clauseBitOffset
  apply List.length_le_of_prefix
  refine ⟨encodeCNFSpinePrefix ((F.drop j).take (k - j)), ?_⟩
  have htake :
      F.take k =
        F.take j ++ (F.drop j).take (k - j) := by
    rw [← List.take_append_drop j (F.take k)]
    have h1 : (F.take k).take j = F.take j := by
      simp [List.take_take, Nat.min_eq_left hjk]
    have h2 :
        (F.take k).drop j =
          (F.drop j).take (k - j) := by
      simpa using List.drop_take_comm F j (k - j)
    rw [h1, h2]
  rw [htake]
  induction F.take j with
  | nil =>
      simp [encodeCNFSpinePrefix]
  | cons c cs ih =>
      simp [encodeCNFSpinePrefix, List.append_assoc]

/-- Bit-region boundaries inherit the clause-region order. -/
theorem bit_region_boundary_order
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    stateBitEnd M x t ≤ headBitEnd M x t ∧
    headBitEnd M x t ≤ leftBitEnd M x t ∧
    leftBitEnd M x t ≤ rightBitEnd M x t ∧
    rightBitEnd M x t ≤ transitionBitEnd M x t ∧
    transitionBitEnd M x t ≤ tableauBitEnd M x t := by
  rcases region_boundary_order M x t with
    ⟨h1, h2, h3, h4, h5⟩
  exact ⟨
    clauseBitOffset_mono _ h1,
    clauseBitOffset_mono _ h2,
    clauseBitOffset_mono _ h3,
    clauseBitOffset_mono _ h4,
    clauseBitOffset_mono _ h5⟩

/-- Physical bit offset of source/right cell i in the full tableau encoding. -/
def fullSourceCellBitOffset
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat) : Nat :=
  tableauClauseBitOffset M x t
    (sourceCellClauseOffset M x t i)

/-- For an in-range source cell, computing its offset from the initial CNF or
from the full tableau gives the same number: later transition/final clauses
cannot affect an earlier encoded prefix. -/
theorem fullSourceCellBitOffset_eq_initial
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t) :
    fullSourceCellBitOffset M x t i =
      sourceCellBitOffset M x t i := by
  unfold fullSourceCellBitOffset tableauClauseBitOffset
  unfold sourceCellBitOffset clauseBitOffset
  have hk :
      sourceCellClauseOffset M x t i ≤
        (ntmInitialCNF M x t).length := by
    rw [← rightClauseEnd_eq_initial_length]
    unfold sourceCellClauseOffset rightClauseEnd
    omega
  have htake :
      (boundedExecTableauCNF_NTM M x t).take
          (sourceCellClauseOffset M x t i) =
        (ntmInitialCNF M x t).take
          (sourceCellClauseOffset M x t i) := by
    unfold boundedExecTableauCNF_NTM
    rw [List.take_append_of_le hk]
  rw [htake]

/-- Bit-level region classifier. -/
inductive TableauBitRegion
  | state
  | head
  | left
  | right
  | transitions
  | finalAcceptance
  | pastEnd
  deriving Repr, DecidableEq

def classifyBit
    (M : PolyNTMCandidate)
    (x : BitString)
    (t j : Nat) : TableauBitRegion :=
  if j < stateBitEnd M x t then
    .state
  else if j < headBitEnd M x t then
    .head
  else if j < leftBitEnd M x t then
    .left
  else if j < rightBitEnd M x t then
    .right
  else if j < transitionBitEnd M x t then
    .transitions
  else if j < tableauBitEnd M x t then
    .finalAcceptance
  else
    .pastEnd

theorem classifyBit_cases
    (M : PolyNTMCandidate)
    (x : BitString)
    (t j : Nat) :
    classifyBit M x t j = .state ∨
    classifyBit M x t j = .head ∨
    classifyBit M x t j = .left ∨
    classifyBit M x t j = .right ∨
    classifyBit M x t j = .transitions ∨
    classifyBit M x t j = .finalAcceptance ∨
    classifyBit M x t j = .pastEnd := by
  unfold classifyBit
  split <;> split <;> split <;> split <;> split <;> split <;>
    simp_all

#print axioms MCore.Real.PNPDiscovery.clauseBitOffset_mono
#print axioms MCore.Real.PNPDiscovery.bit_region_boundary_order
#print axioms MCore.Real.PNPDiscovery.fullSourceCellBitOffset_eq_initial
#print axioms MCore.Real.PNPDiscovery.classifyBit_cases

end PNPDiscovery
end Real
end MCore
