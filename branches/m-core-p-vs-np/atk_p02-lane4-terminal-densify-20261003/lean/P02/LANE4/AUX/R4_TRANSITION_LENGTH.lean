import P02.LANE4.AUX.R4_R5_BOUNDED
import MCore.Real.PNPNTMTableauEncoding

namespace P02
namespace LANE4
namespace AUX
namespace R4_TRANSITION_LENGTH

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding

lemma ntmCopySymbolClauses_length
    (guard : NTMClause)
    (oldVar newVar : Option Bool → Nat) :
    (ntmCopySymbolClauses guard oldVar newVar).length = 6 := by
  simp [ntmCopySymbolClauses, ntmAlphabet]

lemma length_flatMap_range_six
    {α : Type}
    (f : Nat → List α)
    (h : ∀ i, (f i).length = 6)
    (n : Nat) :
    ((List.range n).flatMap f).length = 6 * n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append]
      simp [ih, h n, Nat.mul_succ]

lemma ntmCopyLeftAll_length
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat) :
    (ntmCopyLeftAll guard M x t s).length = 6 * ntmRadius x t := by
  unfold ntmCopyLeftAll
  apply length_flatMap_range_six
  intro i
  exact ntmCopySymbolClauses_length _ _ _

lemma ntmCopyRightAll_length
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat) :
    (ntmCopyRightAll guard M x t s).length = 6 * ntmRadius x t := by
  unfold ntmCopyRightAll
  apply length_flatMap_range_six
  intro i
  exact ntmCopySymbolClauses_length _ _ _

lemma ntmCopyLeftCell_length
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (x : BitString)
    (t oldS oldI newS newI : Nat) :
    (ntmCopyLeftCell guard M x t oldS oldI newS newI).length = 6 := by
  simp [ntmCopyLeftCell, ntmCopySymbolClauses, ntmAlphabet]

lemma ntmCopyRightCell_length
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (x : BitString)
    (t oldS oldI newS newI : Nat) :
    (ntmCopyRightCell guard M x t oldS oldI newS newI).length = 6 := by
  simp [ntmCopyRightCell, ntmCopySymbolClauses, ntmAlphabet]

lemma ntmCopyHeadCell_length
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (t oldS newS : Nat) :
    (ntmCopyHeadCell guard M t oldS newS).length = 6 := by
  simp [ntmCopyHeadCell, ntmCopySymbolClauses, ntmAlphabet]

lemma ntmStayEffectCNF_length
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool) :
    (ntmStayEffectCNF guard M x t s qNext write).length =
      M.stateCount + 4 + 12 * ntmRadius x t := by
  unfold ntmStayEffectCNF
  rw [List.length_append, List.length_append, List.length_append]
  rw [R2_R4_RADIUS.ntmSetStateClauses_length,
      R2_R4_RADIUS.ntmSetSymbolClauses_length,
      ntmCopyLeftAll_length, ntmCopyRightAll_length]
  omega

lemma ntmHaltedStutterCNF_length
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) :
    (ntmHaltedStutterCNF M x t s q a).length =
      M.stateCount + 7 + 12 * ntmRadius x t := by
  unfold ntmHaltedStutterCNF
  rw [List.length_append, List.length_append, List.length_append]
  rw [R2_R4_RADIUS.ntmSetStateClauses_length,
      ntmCopyHeadCell_length,
      ntmCopyLeftAll_length,
      ntmCopyRightAll_length]
  omega

lemma ntmRadius_pos
    (x : BitString) (t : Nat) :
    0 < ntmRadius x t := by
  simp [ntmRadius]

lemma ntmLeftEffectCNF_length
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool) :
    (ntmLeftEffectCNF guard M x t s qNext write).length =
      M.stateCount + 1 + 12 * ntmRadius x t := by
  unfold ntmLeftEffectCNF
  let r := ntmRadius x t
  have hr : 0 < r := by
    simpa [r] using ntmRadius_pos x t
  have hshiftL :
      ((List.range (r - 1)).flatMap fun i =>
        ntmCopyLeftCell guard M x t s (i + 1) (s + 1) i).length =
        6 * (r - 1) := by
    apply length_flatMap_range_six
    intro i
    exact ntmCopyLeftCell_length _ _ _ _ _ _ _ _
  have hshiftR :
      ((List.range (r - 1)).flatMap fun i =>
        ntmCopyRightCell guard M x t s i (s + 1) (i + 1)).length =
        6 * (r - 1) := by
    apply length_flatMap_range_six
    intro i
    exact ntmCopyRightCell_length _ _ _ _ _ _ _ _
  rw [List.length_append, List.length_append, List.length_append,
      List.length_append, List.length_append]
  rw [R2_R4_RADIUS.ntmSetStateClauses_length,
      ntmCopySymbolClauses_length,
      hshiftL,
      R2_R4_RADIUS.ntmSetLeftCell_length,
      R2_R4_RADIUS.ntmSetRightCell_length,
      hshiftR]
  simp [r] at *
  omega

lemma ntmRightEffectCNF_length
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool) :
    (ntmRightEffectCNF guard M x t s qNext write).length =
      M.stateCount + 1 + 12 * ntmRadius x t := by
  unfold ntmRightEffectCNF
  let r := ntmRadius x t
  have hr : 0 < r := by
    simpa [r] using ntmRadius_pos x t
  have hshiftL :
      ((List.range (r - 1)).flatMap fun i =>
        ntmCopyLeftCell guard M x t s i (s + 1) (i + 1)).length =
        6 * (r - 1) := by
    apply length_flatMap_range_six
    intro i
    exact ntmCopyLeftCell_length _ _ _ _ _ _ _ _
  have hshiftR :
      ((List.range (r - 1)).flatMap fun i =>
        ntmCopyRightCell guard M x t s (i + 1) (s + 1) i).length =
        6 * (r - 1) := by
    apply length_flatMap_range_six
    intro i
    exact ntmCopyRightCell_length _ _ _ _ _ _ _ _
  rw [List.length_append, List.length_append, List.length_append,
      List.length_append, List.length_append]
  rw [R2_R4_RADIUS.ntmSetStateClauses_length,
      ntmCopySymbolClauses_length,
      R2_R4_RADIUS.ntmSetLeftCell_length,
      hshiftL, hshiftR,
      R2_R4_RADIUS.ntmSetRightCell_length]
  simp [r] at *
  omega

#print axioms P02.LANE4.AUX.R4_TRANSITION_LENGTH.ntmCopySymbolClauses_length
#print axioms P02.LANE4.AUX.R4_TRANSITION_LENGTH.ntmCopyLeftAll_length
#print axioms P02.LANE4.AUX.R4_TRANSITION_LENGTH.ntmCopyRightAll_length
#print axioms P02.LANE4.AUX.R4_TRANSITION_LENGTH.ntmStayEffectCNF_length
#print axioms P02.LANE4.AUX.R4_TRANSITION_LENGTH.ntmHaltedStutterCNF_length
#print axioms P02.LANE4.AUX.R4_TRANSITION_LENGTH.ntmLeftEffectCNF_length
#print axioms P02.LANE4.AUX.R4_TRANSITION_LENGTH.ntmRightEffectCNF_length

end R4_TRANSITION_LENGTH
end AUX
end LANE4
end P02
