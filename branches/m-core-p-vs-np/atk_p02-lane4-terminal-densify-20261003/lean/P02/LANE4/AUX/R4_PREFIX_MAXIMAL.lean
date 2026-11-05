import P02.LANE4.AUX.R4_PREFIX_SIGNATURE
import P02.LANE4.AUX.R4_R5_BOUNDED

namespace P02
namespace LANE4
namespace AUX
namespace R4_PREFIX_MAXIMAL

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding

/-- Extract the maximal initial run of singleton clauses. -/
def singletonPrefix : NTMCNF → NTMCNF
  | [] => []
  | c :: cs =>
      if c.length = 1 then
        c :: singletonPrefix cs
      else
        []

theorem singletonPrefix_eq_self_of_all_singleton
    (xs : NTMCNF)
    (h : ∀ c ∈ xs, c.length = 1) :
    singletonPrefix xs = xs := by
  induction xs with
  | nil =>
      rfl
  | cons c cs ih =>
      have hc : c.length = 1 := h c (by simp)
      have hcs : ∀ d ∈ cs, d.length = 1 := by
        intro d hd
        exact h d (by simp [hd])
      simp [singletonPrefix, hc, ih hcs]

/-- A singleton prefix followed by a non-singleton head is recovered exactly. -/
theorem singletonPrefix_append_stop
    (xs : NTMCNF)
    (c : NTMClause)
    (cs : NTMCNF)
    (hxs : ∀ d ∈ xs, d.length = 1)
    (hc : c.length ≠ 1) :
    singletonPrefix (xs ++ c :: cs) = xs := by
  induction xs with
  | nil =>
      simp [singletonPrefix, hc]
  | cons d ds ih =>
      have hd : d.length = 1 := hxs d (by simp)
      have hds : ∀ e ∈ ds, e.length = 1 := by
        intro e he
        exact hxs e (by simp [he])
      simp [singletonPrefix, hd, ih hds]

/-- If the transition block starts with a non-singleton clause, the initial
tableau block is the maximal singleton prefix of initial++transitions. -/
theorem singletonPrefix_initial_append_transitions
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (c : NTMClause)
    (cs : NTMCNF)
    (htrans : ntmTransitionsCNF M x t = c :: cs)
    (hc : c.length ≠ 1) :
    singletonPrefix
      (ntmInitialCNF M x t ++ ntmTransitionsCNF M x t) =
      ntmInitialCNF M x t := by
  rw [htrans]
  apply singletonPrefix_append_stop
  · intro d hd
    exact R4_PREFIX_SIGNATURE.ntmInitialCNF_clause_length_one M x t d hd
  · exact hc

/-- Under the same concrete transition-head condition, equality of
initial++transition blocks forces equality of the initial blocks. -/
theorem initial_eq_of_concat_eq_with_transition_heads
    {M : PolyNTMCandidate}
    {x y : BitString}
    {t : Nat}
    {cx cy : NTMClause}
    {tx ty : NTMCNF}
    (hx : ntmTransitionsCNF M x t = cx :: tx)
    (hy : ntmTransitionsCNF M y t = cy :: ty)
    (hcx : cx.length ≠ 1)
    (hcy : cy.length ≠ 1)
    (h :
      ntmInitialCNF M x t ++ ntmTransitionsCNF M x t =
      ntmInitialCNF M y t ++ ntmTransitionsCNF M y t) :
    ntmInitialCNF M x t = ntmInitialCNF M y t := by
  have hs := congrArg singletonPrefix h
  rw [singletonPrefix_initial_append_transitions M x t cx tx hx hcx,
      singletonPrefix_initial_append_transitions M y t cy ty hy hcy] at hs
  exact hs

/-- At zero fuel the transition block vanishes, so the common final block can
be cancelled directly from equality of whole tableaux. -/
theorem tableau_initial_eq_zero
    {M : PolyNTMCandidate}
    {x y : BitString}
    (h :
      boundedExecTableauCNF_NTM M x 0 =
      boundedExecTableauCNF_NTM M y 0) :
    ntmInitialCNF M x 0 = ntmInitialCNF M y 0 := by
  have h' :
      ntmInitialCNF M x 0 ++ ntmFinalAcceptanceCNF M 0 =
      ntmInitialCNF M y 0 ++ ntmFinalAcceptanceCNF M 0 := by
    simpa [boundedExecTableauCNF_NTM, ntmTransitionsCNF] using h
  exact List.append_right_cancel h'

#print axioms P02.LANE4.AUX.R4_PREFIX_MAXIMAL.singletonPrefix_eq_self_of_all_singleton
#print axioms P02.LANE4.AUX.R4_PREFIX_MAXIMAL.singletonPrefix_append_stop
#print axioms P02.LANE4.AUX.R4_PREFIX_MAXIMAL.initial_eq_of_concat_eq_with_transition_heads
#print axioms P02.LANE4.AUX.R4_PREFIX_MAXIMAL.tableau_initial_eq_zero

end R4_PREFIX_MAXIMAL
end AUX
end LANE4
end P02
