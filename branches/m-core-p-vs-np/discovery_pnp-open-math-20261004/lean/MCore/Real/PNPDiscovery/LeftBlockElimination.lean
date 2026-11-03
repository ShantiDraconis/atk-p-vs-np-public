import MCore.Real.PNPDiscovery.RightCellInjectivity

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding

/-- Entire time-zero left-tape block.  For canonical input tapes its symbols
are all blank; only layout parameters can vary. -/
def initialLeftBlock
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : NTMCNF :=
  (List.range (ntmRadius x t)).flatMap fun i =>
    ntmSetLeftCell [] M x t 0 i
      ((inputTape x).left.getD i M.machine.blank)

/-- One left-cell block is independent of source contents once source length
and clock are fixed. -/
theorem initialLeftCell_eq_of_length
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t i : Nat)
    (hLen : x.length = y.length) :
    ntmSetLeftCell [] M x t 0 i
        ((inputTape x).left.getD i M.machine.blank) =
      ntmSetLeftCell [] M y t 0 i
        ((inputTape y).left.getD i M.machine.blank) := by
  unfold ntmSetLeftCell
  have hvar :
      (ntmLeftVar M x t 0 i) =
        (ntmLeftVar M y t 0 i) := by
    funext a
    exact ntmLeftVar_eq_of_length_eq M a hLen
  rw [hvar]
  cases x <;> cases y <;> simp [inputTape]

/-- Consequently the whole left block is identical for equal-length inputs at
equal clock. -/
theorem initialLeftBlock_eq_of_length_clock
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t u : Nat)
    (hLen : x.length = y.length)
    (hClock : t = u) :
    initialLeftBlock M x t =
      initialLeftBlock M y u := by
  subst u
  unfold initialLeftBlock
  have hRadius :
      ntmRadius x t = ntmRadius y t :=
    ntmRadius_eq_of_length_eq hLen
  rw [hRadius]
  have hfun :
      (fun i =>
        ntmSetLeftCell [] M x t 0 i
          ((inputTape x).left.getD i M.machine.blank)) =
      (fun i =>
        ntmSetLeftCell [] M y t 0 i
          ((inputTape y).left.getD i M.machine.blank)) := by
    funext i
    exact initialLeftCell_eq_of_length M x y t i hLen
  rw [hfun]

/-- Decompose the time-zero CNF into the four literal regions that matter for
source-dependency analysis. -/
theorem ntmInitialCNF_four_blocks
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    ntmInitialCNF M x t =
      ntmSetStateClauses [] M t 0 M.machine.initial ++
      initialHeadBlock M x t ++
      initialLeftBlock M x t ++
      (List.range (ntmRadius x t)).flatMap
        (fun i => initialRightCellBlock M x t i) := by
  unfold ntmInitialCNF initialHeadBlock initialLeftBlock
  unfold initialRightCellBlock sourceHeadSymbol sourceRightSymbol
  rfl

/-- After state/head alignment, equal length+clock automatically aligns the
entire intervening left block. -/
structure StateHeadLeftAlignment
    (M : PolyNTMCandidate)
    (x y : BitString) : Prop where
  length_eq : x.length = y.length
  clock_eq :
    M.timeBound x.length = M.timeBound y.length
  head_eq :
    sourceHeadSymbol x = sourceHeadSymbol y

theorem stateHeadLeftAlignment_left_eq
    (M : PolyDTMCandidate)
    (x y : BitString)
    (H : StateHeadLeftAlignment
      (complementToNTMCandidate M) x y) :
    initialLeftBlock
        (complementToNTMCandidate M)
        x (M.timeBound x.length) =
      initialLeftBlock
        (complementToNTMCandidate M)
        y (M.timeBound y.length) := by
  exact initialLeftBlock_eq_of_length_clock
    (complementToNTMCandidate M)
    x y
    (M.timeBound x.length)
    (M.timeBound y.length)
    H.length_eq H.clock_eq

#print axioms MCore.Real.PNPDiscovery.initialLeftCell_eq_of_length
#print axioms MCore.Real.PNPDiscovery.initialLeftBlock_eq_of_length_clock
#print axioms MCore.Real.PNPDiscovery.ntmInitialCNF_four_blocks
#print axioms MCore.Real.PNPDiscovery.stateHeadLeftAlignment_left_eq

end PNPDiscovery
end Real
end MCore
