import MCore.Real.PNPDiscovery.TableauShapeLeakage

namespace MCore
namespace Real
namespace PNPDiscovery

open PNPNTMTableauEncoding

/-- Every active transition case contains at least its guard clause. -/
theorem ntmActiveChoiceCNF_nonempty
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ntmActiveChoiceCNF M x t s q a ≠ [] := by
  simp [ntmActiveChoiceCNF]

/-- Every halted-stutter case contains state-copy clauses because the machine
has stateCount+1 states. -/
theorem ntmHaltedStutterCNF_nonempty
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ntmHaltedStutterCNF M x t s q a ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  simp [ntmHaltedStutterCNF, ntmStateCount] at hlen

/-- Hence every transition case contributes at least one clause. -/
theorem ntmTransitionCaseCNF_nonempty
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ntmTransitionCaseCNF M x t s q a ≠ [] := by
  unfold ntmTransitionCaseCNF
  split
  · exact ntmHaltedStutterCNF_nonempty M x t s q a
  · exact ntmActiveChoiceCNF_nonempty M x t s q a

/-- Every time slice contributes at least one clause. -/
theorem ntmTransitionStepCNF_nonempty
    (M : PolyNTMCandidate)
    (x : BitString)
    (t s : Nat) :
    ntmTransitionStepCNF M x t s ≠ [] := by
  let q0 : Fin (M.stateCount + 1) := ⟨0, by omega⟩
  have hcase :=
    ntmTransitionCaseCNF_nonempty M x t s q0 none
  unfold ntmTransitionStepCNF
  intro h
  have hmemq :
      (ntmAlphabet.flatMap fun a =>
        ntmTransitionCaseCNF M x t s q0 a) ∈
      List.ofFn (fun q : Fin (M.stateCount + 1) =>
        ntmAlphabet.flatMap fun a =>
          ntmTransitionCaseCNF M x t s q a) := by
    exact List.mem_ofFn.mpr ⟨q0, rfl⟩
  have hnone : none ∈ ntmAlphabet := by
    simp [ntmAlphabet]
  have hsub :
      ntmTransitionCaseCNF M x t s q0 none ≠ [] :=
    hcase
  have hflatNonempty :
      (ntmAlphabet.flatMap fun a =>
        ntmTransitionCaseCNF M x t s q0 a) ≠ [] := by
    intro hz
    have hm :
        ∀ a ∈ ntmAlphabet,
          ntmTransitionCaseCNF M x t s q0 a = [] := by
      intro a ha
      have := congrArg List.length hz
      simp at this
      exact List.length_eq_zero.mp
        (Nat.eq_zero_of_le_zero
          (by
            have hx :
                (ntmTransitionCaseCNF M x t s q0 a).length ≤
                  (ntmAlphabet.flatMap fun b =>
                    ntmTransitionCaseCNF M x t s q0 b).length := by
              apply List.length_le_of_sublist
              exact List.Sublist.flatMap
                (List.Sublist.refl ntmAlphabet)
                (fun _ _ => List.Sublist.refl _)
            simpa [hz] using hx))
    exact hsub (hm none hnone)
  have hall :
      (List.ofFn (fun q : Fin (M.stateCount + 1) =>
        ntmAlphabet.flatMap fun a =>
          ntmTransitionCaseCNF M x t s q a)).flatten = [] := h
  have hparts :
      ∀ xs ∈
        List.ofFn (fun q : Fin (M.stateCount + 1) =>
          ntmAlphabet.flatMap fun a =>
            ntmTransitionCaseCNF M x t s q a),
        xs = [] := by
    intro xs hxs
    have := congrArg List.length hall
    simp at this
    have hx :
        xs.length ≤
          (List.ofFn (fun q : Fin (M.stateCount + 1) =>
            ntmAlphabet.flatMap fun a =>
              ntmTransitionCaseCNF M x t s q a)).flatten.length := by
      apply List.length_le_of_sublist
      exact List.sublist_flatten hxs
    simp [hall] at hx
    exact List.length_eq_zero.mp (Nat.eq_zero_of_le_zero hx)
  exact hflatNonempty (hparts _ hmemq)

/-- Number of transition clauses is at least the declared number of slices. -/
theorem time_le_ntmTransitionsCNF_length
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) :
    t ≤ (ntmTransitionsCNF M x t).length := by
  unfold ntmTransitionsCNF
  induction t with
  | zero =>
      simp
  | succ t ih =>
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_singleton, List.length_append]
      have hpos :
          0 < (ntmTransitionStepCNF M x (t + 1) t).length := by
        exact List.length_pos.mpr
          (ntmTransitionStepCNF_nonempty M x (t + 1) t)
      omega

/-- Mechanical shape bridge still to close for the compensated-radius branch.
This is deliberately a size theorem, not a complexity endpoint. -/
def EqualRadiusTransitionShapeGap : Prop :=
  ∀ (M : PolyNTMCandidate)
    (x y : BitString)
    (t u : Nat),
    ntmRadius x t = ntmRadius y u →
    t ≠ u →
    (boundedExecTableauCNF_NTM M x t).length ≠
      (boundedExecTableauCNF_NTM M y u).length

#print axioms MCore.Real.PNPDiscovery.ntmTransitionCaseCNF_nonempty
#print axioms MCore.Real.PNPDiscovery.ntmTransitionStepCNF_nonempty
#print axioms MCore.Real.PNPDiscovery.time_le_ntmTransitionsCNF_length

end PNPDiscovery
end Real
end MCore
