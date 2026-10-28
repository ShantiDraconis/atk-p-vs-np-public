import P02.LANE4.AUX.R2_R4_RADIUS
import P02.LANE4.AUX.R1_R3_REAL
import MCore.Real.PNPNTMTableauEncoding

namespace P02
namespace LANE4
namespace AUX
namespace R4_INITIAL_INJECTIVE

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding

/-- The 3-clause symbol setter is injective in its target.  Variable numbering
is irrelevant here: the target is recorded by the polarity pattern. -/
theorem ntmSetSymbolClauses_target_injective
    (varAt : Option Bool → Nat) :
    Function.Injective (ntmSetSymbolClauses [] varAt) := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [ntmSetSymbolClauses, ntmAlphabet, ntmLitFor, ntmPos, ntmNeg] at h ⊢

/-- Length of the left initial-cell block. -/
theorem ntmInitialLeftBlock_length
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    ((List.range (ntmRadius x t)).flatMap (fun i =>
      ntmSetLeftCell [] M x t 0 i
        ((inputTape x).left.getD i M.machine.blank))).length =
      3 * ntmRadius x t := by
  apply R2_R4_RADIUS.length_flatMap_range_three
  intro i
  exact R2_R4_RADIUS.ntmSetLeftCell_length [] M x t 0 i _

/-- Length of the right initial-cell block. -/
theorem ntmInitialRightBlock_length
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    ((List.range (ntmRadius x t)).flatMap (fun i =>
      ntmSetRightCell [] M x t 0 i
        ((inputTape x).right.getD i M.machine.blank))).length =
      3 * ntmRadius x t := by
  apply R2_R4_RADIUS.length_flatMap_range_three
  intro i
  exact R2_R4_RADIUS.ntmSetRightCell_length [] M x t 0 i _

/-- The head setter is the three-clause block immediately after the fixed
state block. -/
theorem ntmInitialCNF_extract_head
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    ((ntmInitialCNF M x t).drop (M.stateCount + 1)).take 3 =
      ntmSetSymbolClauses [] (ntmHeadVar M t 0) (inputTape x).head := by
  simp [ntmInitialCNF,
    R2_R4_RADIUS.ntmSetStateClauses_length,
    R2_R4_RADIUS.ntmSetSymbolClauses_length]

/-- Equality of initial blocks therefore recovers the tape head. -/
theorem ntmInitialCNF_eq_implies_head_eq
    {M : PolyNTMCandidate} {x y : BitString} {t : Nat}
    (h : ntmInitialCNF M x t = ntmInitialCNF M y t) :
    (inputTape x).head = (inputTape y).head := by
  have hb := congrArg
    (fun f : NTMCNF => (f.drop (M.stateCount + 1)).take 3) h
  rw [ntmInitialCNF_extract_head M x t,
      ntmInitialCNF_extract_head M y t] at hb
  exact ntmSetSymbolClauses_target_injective (ntmHeadVar M t 0) hb

/-- The suffix after state+head+left is exactly the right-cell block. -/
theorem ntmInitialCNF_extract_right
    (M : PolyNTMCandidate) (x : BitString) (t : Nat) :
    (ntmInitialCNF M x t).drop
      (M.stateCount + 4 + 3 * ntmRadius x t) =
    (List.range (ntmRadius x t)).flatMap (fun i =>
      ntmSetRightCell [] M x t 0 i
        ((inputTape x).right.getD i M.machine.blank)) := by
  simp [ntmInitialCNF,
    R2_R4_RADIUS.ntmSetStateClauses_length,
    R2_R4_RADIUS.ntmSetSymbolClauses_length,
    ntmInitialLeftBlock_length]

/-- A sequence of 3-clause symbol blocks is pointwise injective in the target
sequence. -/
theorem symbolBlocks_targets_eq
    (n : Nat)
    (varAt : Nat → Option Bool → Nat)
    (f g : Nat → Option Bool)
    (h :
      (List.range n).flatMap
          (fun i => ntmSetSymbolClauses [] (varAt i) (f i)) =
      (List.range n).flatMap
          (fun i => ntmSetSymbolClauses [] (varAt i) (g i))) :
    ∀ i, i < n → f i = g i := by
  induction n with
  | zero =>
      intro i hi
      omega
  | succ n ih =>
      have hlast := congrArg (fun z : NTMCNF => z.drop (3 * n)) h
      have hfn :
          ((List.range n).flatMap
            (fun i => ntmSetSymbolClauses [] (varAt i) (f i))).length =
            3 * n := by
        apply R2_R4_RADIUS.length_flatMap_range_three
        intro i
        exact R2_R4_RADIUS.ntmSetSymbolClauses_length [] (varAt i) (f i)
      have hgn :
          ((List.range n).flatMap
            (fun i => ntmSetSymbolClauses [] (varAt i) (g i))).length =
            3 * n := by
        apply R2_R4_RADIUS.length_flatMap_range_three
        intro i
        exact R2_R4_RADIUS.ntmSetSymbolClauses_length [] (varAt i) (g i)
      have htarget : f n = g n := by
        apply ntmSetSymbolClauses_target_injective (varAt n)
        simpa [List.range_succ, hfn, hgn] using hlast
      have hpref := congrArg (fun z : NTMCNF => z.take (3 * n)) h
      have hp :
          (List.range n).flatMap
              (fun i => ntmSetSymbolClauses [] (varAt i) (f i)) =
          (List.range n).flatMap
              (fun i => ntmSetSymbolClauses [] (varAt i) (g i)) := by
        simpa [List.range_succ, hfn, hgn] using hpref
      intro i hi
      by_cases hin : i = n
      · simpa [hin] using htarget
      · exact ih hp i (by omega)

/-- Same-length lists are equal when their getD values agree on their valid
indices. -/
theorem list_eq_of_length_eq_getD_eq
    {α : Type}
    (d : α)
    (xs ys : List α)
    (hlen : xs.length = ys.length)
    (hget : ∀ i, i < xs.length → xs.getD i d = ys.getD i d) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      simpa using hlen.symm
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hlen
      | cons y ys =>
          have hxy := hget 0 (by simp)
          have hlen' : xs.length = ys.length := by simpa using hlen
          have htail :
              ∀ i, i < xs.length → xs.getD i d = ys.getD i d := by
            intro i hi
            have hnext := hget (i + 1) (by simp [hi])
            simpa using hnext
          have hrest := ih ys hlen' htail
          have hxy' : x = y := by simpa using hxy
          simpa [hxy', hrest]

theorem inputTape_right_length
    (x : BitString) :
    (inputTape x).right.length = x.length - 1 := by
  cases x <;> simp [inputTape]

/-- At fixed M,t, equality of initial CNFs recovers the complete canonical
input tape and therefore the source bitstring. -/
theorem ntmInitialCNF_injective_fixed
    (M : PolyNTMCandidate) (t : Nat) :
    Function.Injective (fun x => ntmInitialCNF M x t) := by
  intro x y h
  have hradius := R2_R4_RADIUS.initial_radius_extract h
  have hlen : x.length = y.length := R2_R4_RADIUS.initial_dim_extract_real h
  have hhead := ntmInitialCNF_eq_implies_head_eq h

  have hrightBlocks := congrArg
    (fun f : NTMCNF =>
      f.drop (M.stateCount + 4 + 3 * ntmRadius x t)) h
  rw [ntmInitialCNF_extract_right M x t] at hrightBlocks
  have hyright :
      (ntmInitialCNF M y t).drop
          (M.stateCount + 4 + 3 * ntmRadius x t) =
      (List.range (ntmRadius y t)).flatMap (fun i =>
        ntmSetRightCell [] M y t 0 i
          ((inputTape y).right.getD i M.machine.blank)) := by
    simpa [hradius] using ntmInitialCNF_extract_right M y t
  rw [hyright] at hrightBlocks

  have hvar :
      ∀ i a,
        ntmRightVar M x t 0 i a = ntmRightVar M y t 0 i a := by
    intro i a
    simp [ntmRightVar, ntmRightBase, ntmLeftBase, hradius]

  have htargets :
      ∀ i, i < ntmRadius x t →
        (inputTape x).right.getD i M.machine.blank =
        (inputTape y).right.getD i M.machine.blank := by
    have hb := hrightBlocks
    simp only [ntmSetRightCell] at hb
    have hb' :
        (List.range (ntmRadius x t)).flatMap (fun i =>
          ntmSetSymbolClauses [] (ntmRightVar M x t 0 i)
            ((inputTape x).right.getD i M.machine.blank)) =
        (List.range (ntmRadius x t)).flatMap (fun i =>
          ntmSetSymbolClauses [] (ntmRightVar M x t 0 i)
            ((inputTape y).right.getD i M.machine.blank)) := by
      simpa [hradius, hvar] using hb
    exact symbolBlocks_targets_eq
      (ntmRadius x t)
      (fun i => ntmRightVar M x t 0 i)
      (fun i => (inputTape x).right.getD i M.machine.blank)
      (fun i => (inputTape y).right.getD i M.machine.blank)
      hb'

  have hrightLen :
      (inputTape x).right.length = (inputTape y).right.length := by
    simp [inputTape_right_length, hlen]

  have hright :
      (inputTape x).right = (inputTape y).right := by
    apply list_eq_of_length_eq_getD_eq M.machine.blank
      (inputTape x).right (inputTape y).right hrightLen
    intro i hi
    apply htargets i
    have hri : (inputTape x).right.length ≤ x.length := by
      simp [inputTape_right_length]
    have : i < x.length := Nat.lt_of_lt_of_le hi hri
    simp [ntmRadius]
    omega

  have htape : inputTape x = inputTape y := by
    cases hx : inputTape x
    cases hy : inputTape y
    simp_all [inputTape]
  exact R1_R3_REAL.inputTape_injective htape

#print axioms P02.LANE4.AUX.R4_INITIAL_INJECTIVE.ntmSetSymbolClauses_target_injective
#print axioms P02.LANE4.AUX.R4_INITIAL_INJECTIVE.ntmInitialCNF_eq_implies_head_eq
#print axioms P02.LANE4.AUX.R4_INITIAL_INJECTIVE.symbolBlocks_targets_eq
#print axioms P02.LANE4.AUX.R4_INITIAL_INJECTIVE.ntmInitialCNF_injective_fixed

end R4_INITIAL_INJECTIVE
end AUX
end LANE4
end P02
