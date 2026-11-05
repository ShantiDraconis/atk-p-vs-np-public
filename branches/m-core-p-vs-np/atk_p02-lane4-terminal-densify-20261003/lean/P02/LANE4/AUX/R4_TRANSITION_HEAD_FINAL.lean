import P02.LANE4.AUX.R4_TRANSITION_HEAD
import P02.LANE4.AUX.R4_PREFIX_MAXIMAL

namespace P02
namespace LANE4
namespace AUX
namespace R4_TRANSITION_HEAD_FINAL

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding

/-- The first transition case at any step is the case for state index 0 and
symbol `none`.  Since `stateCount + 1` is nonzero and `ntmAlphabet`
starts with `none`, the transition step inherits the non-singleton head
proved for every transition case. -/
theorem ntmTransitionStepCNF_head_non_singleton
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat) :
    ∃ c cs,
      ntmTransitionStepCNF M x t s = c :: cs ∧
      2 ≤ c.length := by
  let q0 : Fin (M.stateCount + 1) :=
    ⟨0, by omega⟩
  obtain ⟨c, cs, hcase, hlen⟩ :=
    R4_TRANSITION_HEAD.ntmTransitionCaseCNF_head_non_singleton
      M x t s q0 none
  refine ⟨c, ?_, ?_, hlen⟩
  · exact
      cs ++
        (ntmTransitionCaseCNF M x t s q0 (some false) ++
         ntmTransitionCaseCNF M x t s q0 (some true)) ++
        ((List.ofFn fun q : Fin M.stateCount =>
          ntmAlphabet.flatMap fun a =>
            ntmTransitionCaseCNF M x t s
              ⟨q.val + 1, by omega⟩ a).flatten)
  · simp [ntmTransitionStepCNF, ntmAlphabet, q0, hcase,
      List.append_assoc]

/-- Positive time means `List.range t` begins with step 0, so the complete
transition block has the same non-singleton head as transition step 0. -/
theorem ntmTransitionsCNF_head_non_singleton
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (ht : 0 < t) :
    ∃ c cs,
      ntmTransitionsCNF M x t = c :: cs ∧
      2 ≤ c.length := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  obtain ⟨c, cs, hstep, hlen⟩ :=
    ntmTransitionStepCNF_head_non_singleton M x (n + 1) 0
  refine ⟨c, ?_, ?_, hlen⟩
  · exact
      cs ++
        ((List.range' 1 n).flatMap fun s =>
          ntmTransitionStepCNF M x (n + 1) s)
  · simp [ntmTransitionsCNF, List.range_succ_eq_map, hstep]

#print axioms P02.LANE4.AUX.R4_TRANSITION_HEAD_FINAL.ntmTransitionStepCNF_head_non_singleton
#print axioms P02.LANE4.AUX.R4_TRANSITION_HEAD_FINAL.ntmTransitionsCNF_head_non_singleton

end R4_TRANSITION_HEAD_FINAL
end AUX
end LANE4
end P02
