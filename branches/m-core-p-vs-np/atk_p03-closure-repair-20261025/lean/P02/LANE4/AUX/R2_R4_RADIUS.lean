import P02.LANE4.AUX.R1_R3_REAL
import MCore.Real.PNPNTMTableauEncoding

namespace P02
namespace LANE4
namespace AUX
namespace R2_R4_RADIUS

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding

lemma ntmSetStateClauses_length
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (t s : Nat)
    (target : Fin (M.stateCount + 1)) :
    (ntmSetStateClauses guard M t s target).length = M.stateCount + 1 := by
  simp [ntmSetStateClauses]

lemma ntmSetSymbolClauses_length
    (guard : NTMClause)
    (varAt : Option Bool → Nat)
    (target : Option Bool) :
    (ntmSetSymbolClauses guard varAt target).length = 3 := by
  simp [ntmSetSymbolClauses, ntmAlphabet]

lemma ntmSetLeftCell_length
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s i : Nat)
    (target : Option Bool) :
    (ntmSetLeftCell guard M x t s i target).length = 3 := by
  simp [ntmSetLeftCell, ntmSetSymbolClauses, ntmAlphabet]

lemma ntmSetRightCell_length
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s i : Nat)
    (target : Option Bool) :
    (ntmSetRightCell guard M x t s i target).length = 3 := by
  simp [ntmSetRightCell, ntmSetSymbolClauses, ntmAlphabet]

lemma length_flatMap_range_three
    {α : Type}
    (f : Nat → List α)
    (h : ∀ i, (f i).length = 3)
    (n : Nat) :
    ((List.range n).flatMap f).length = 3 * n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append]
      simp [ih, h n, Nat.mul_succ]

/-- Exact syntactic size of the initial tableau block.  This is an AUX fact:
it contains no complexity-theoretic endpoint assumption. -/
theorem ntmInitialCNF_length_exact
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    (ntmInitialCNF M x t).length =
      M.stateCount + 4 + 6 * ntmRadius x t := by
  unfold ntmInitialCNF
  rw [List.length_append, List.length_append, List.length_append]
  rw [ntmSetStateClauses_length, ntmSetSymbolClauses_length]
  have hleft :
      ((List.range (ntmRadius x t)).flatMap (fun i =>
        ntmSetLeftCell [] M x t 0 i
          ((inputTape x).left.getD i M.machine.blank))).length =
        3 * ntmRadius x t := by
    apply length_flatMap_range_three
    intro i
    exact ntmSetLeftCell_length [] M x t 0 i _
  have hright :
      ((List.range (ntmRadius x t)).flatMap (fun i =>
        ntmSetRightCell [] M x t 0 i
          ((inputTape x).right.getD i M.machine.blank))).length =
        3 * ntmRadius x t := by
    apply length_flatMap_range_three
    intro i
    exact ntmSetRightCell_length [] M x t 0 i _
  rw [hleft, hright]
  omega

/-- Equality of initial CNF blocks reflects equality of tableau radius. -/
theorem initial_radius_extract
    {M : PolyNTMCandidate}
    {x y : BitString}
    {t : Nat}
    (h : ntmInitialCNF M x t = ntmInitialCNF M y t) :
    ntmRadius x t = ntmRadius y t := by
  have hlen := congrArg List.length h
  rw [ntmInitialCNF_length_exact M x t,
      ntmInitialCNF_length_exact M y t] at hlen
  omega

/-- Honest dimension extraction from equality of initial CNF blocks. -/
theorem initial_dim_extract_real
    {M : PolyNTMCandidate}
    {x y : BitString}
    {t : Nat}
    (h : ntmInitialCNF M x t = ntmInitialCNF M y t) :
    x.length = y.length := by
  have hr := initial_radius_extract h
  unfold ntmRadius at hr
  omega

#print axioms P02.LANE4.AUX.R2_R4_RADIUS.ntmInitialCNF_length_exact
#print axioms P02.LANE4.AUX.R2_R4_RADIUS.initial_radius_extract
#print axioms P02.LANE4.AUX.R2_R4_RADIUS.initial_dim_extract_real

end R2_R4_RADIUS
end AUX
end LANE4
end P02
