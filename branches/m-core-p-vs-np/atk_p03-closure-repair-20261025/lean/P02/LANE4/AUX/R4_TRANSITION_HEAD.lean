import P02.LANE4.AUX.R4_PREFIX_MAXIMAL
import P02.LANE4.AUX.R4_TRANSITION_LENGTH

namespace P02
namespace LANE4
namespace AUX
namespace R4_TRANSITION_HEAD

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding

/-- Every state-setting clause has the guard plus one literal. -/
theorem ntmSetStateClauses_clause_length
    (guard : NTMClause)
    (M : PolyNTMCandidate)
    (t s : Nat)
    (target : Fin (M.stateCount + 1))
    (c : NTMClause)
    (hc : c ∈ ntmSetStateClauses guard M t s target) :
    c.length = guard.length + 1 := by
  simp [ntmSetStateClauses] at hc
  rcases hc with ⟨q, rfl⟩
  simp

/-- Every symbol-setting clause has the guard plus one literal. -/
theorem ntmSetSymbolClauses_clause_length
    (guard : NTMClause)
    (varAt : Option Bool → Nat)
    (target : Option Bool)
    (c : NTMClause)
    (hc : c ∈ ntmSetSymbolClauses guard varAt target) :
    c.length = guard.length + 1 := by
  simp [ntmSetSymbolClauses, ntmAlphabet] at hc
  rcases hc with rfl | rfl | rfl
  all_goals simp

/-- The halted-stutter block is nonempty and its first clause is guarded by two
literals, hence has length at least two. -/
theorem ntmHaltedStutterCNF_head_non_singleton
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ∃ c cs,
      ntmHaltedStutterCNF M x t s q a = c :: cs ∧
      2 ≤ c.length := by
  let guard : NTMClause :=
    [ntmNeg (ntmStateVar M t s q), ntmNeg (ntmHeadVar M t s a)]
  have hlen :
      (ntmSetStateClauses guard M t (s + 1) q).length =
        M.stateCount + 1 :=
    R2_R4_RADIUS.ntmSetStateClauses_length guard M t (s + 1) q
  cases hstate : ntmSetStateClauses guard M t (s + 1) q with
  | nil =>
      simp [hstate] at hlen
  | cons c cs =>
      refine ⟨c,
        cs ++ ntmCopyHeadCell guard M t s (s + 1) ++
          ntmCopyLeftAll guard M x t s ++
          ntmCopyRightAll guard M x t s, ?_, ?_⟩
      · simp [ntmHaltedStutterCNF, guard, hstate, List.append_assoc]
      · have hc :
            c.length = guard.length + 1 := by
          apply ntmSetStateClauses_clause_length guard M t (s + 1) q c
          rw [hstate]
          simp
        simp [guard] at hc
        omega

/-- The active-choice block begins with the explicit guard-choice clause. -/
theorem ntmActiveChoiceCNF_head_non_singleton
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ∃ c cs,
      ntmActiveChoiceCNF M x t s q a = c :: cs ∧
      2 ≤ c.length := by
  let c := ntmGuardChoiceClause M x t s q a
  refine ⟨c,
    (ntmIndexedTransitions (M.machine.transition q a)).flatMap
        (fun p => ntmChoiceGuardCNF M x t s q a p.1) ++
      ntmAtMostOneChoiceCNF M x t s q a ++
      (ntmIndexedTransitions (M.machine.transition q a)).flatMap
        (fun p => ntmChoiceEffectCNF M x t s q a p), ?_, ?_⟩
  · simp [ntmActiveChoiceCNF, c, List.append_assoc]
  · simpa [c] using
      R4_PREFIX_SIGNATURE.ntmGuardChoiceClause_length_ge_two M x t s q a

/-- Every transition case has a non-singleton head, whether the machine is
already halted or still active. -/
theorem ntmTransitionCaseCNF_head_non_singleton
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ∃ c cs,
      ntmTransitionCaseCNF M x t s q a = c :: cs ∧
      2 ≤ c.length := by
  unfold ntmTransitionCaseCNF
  split
  · exact ntmHaltedStutterCNF_head_non_singleton M x t s q a
  · exact ntmActiveChoiceCNF_head_non_singleton M x t s q a

#print axioms P02.LANE4.AUX.R4_TRANSITION_HEAD.ntmSetStateClauses_clause_length
#print axioms P02.LANE4.AUX.R4_TRANSITION_HEAD.ntmHaltedStutterCNF_head_non_singleton
#print axioms P02.LANE4.AUX.R4_TRANSITION_HEAD.ntmActiveChoiceCNF_head_non_singleton
#print axioms P02.LANE4.AUX.R4_TRANSITION_HEAD.ntmTransitionCaseCNF_head_non_singleton

end R4_TRANSITION_HEAD
end AUX
end LANE4
end P02
