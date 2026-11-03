import P02.LANE4.AUX.R4_TRANSITION_HEAD_FINAL
import P02.LANE4.AUX.R4_PREFIX_MAXIMAL
import P02.LANE4.AUX.R4_INITIAL_INJECTIVE
import P02.LANE4.AUX.R4_R5_BOUNDED

namespace P02
namespace LANE4
namespace AUX
namespace R4_FINAL

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding

/-- Whole-tableau equality recovers the initial block for every t.  At t=0
the transition block is empty; at positive t the transition head is
non-singleton and the maximal-singleton-prefix extractor applies. -/
theorem tableau_initial_eq_of_whole
    {M : PolyNTMCandidate}
    {x y : BitString}
    {t : Nat}
    (h :
      boundedExecTableauCNF_NTM M x t =
      boundedExecTableauCNF_NTM M y t) :
    ntmInitialCNF M x t = ntmInitialCNF M y t := by
  by_cases ht : t = 0
  · subst t
    exact R4_PREFIX_MAXIMAL.tableau_initial_eq_zero h
  · have htpos : 0 < t := by omega
    obtain ⟨cx, tx, hx, hcx⟩ :=
      R4_TRANSITION_HEAD_FINAL.ntmTransitionsCNF_head_non_singleton
        M x t htpos
    obtain ⟨cy, ty, hy, hcy⟩ :=
      R4_TRANSITION_HEAD_FINAL.ntmTransitionsCNF_head_non_singleton
        M y t htpos
    have hconcat :=
      R4_R5_BOUNDED.boundedExecTableau_eq_without_final h
    apply R4_PREFIX_MAXIMAL.initial_eq_of_concat_eq_with_transition_heads
      hx hy
    · omega
    · omega
    · exact hconcat

/-- R4: at fixed machine and fixed fuel, the bounded tableau CNF is injective
in the source bitstring. -/
theorem boundedExecTableau_same_params_injective
    (M : PolyNTMCandidate)
    (t : Nat) :
    Function.Injective (fun x => boundedExecTableauCNF_NTM M x t) := by
  intro x y h
  have hinit := tableau_initial_eq_of_whole h
  exact R4_INITIAL_INJECTIVE.ntmInitialCNF_injective_fixed M t hinit

/-- R4 at Circuit level. -/
theorem boundedExecCircuit_same_params_injective
    (M : PolyNTMCandidate)
    (t : Nat) :
    Function.Injective (fun x => boundedExecCircuit_NTM M x t) := by
  intro x y h
  have htab :=
    R4_R5_BOUNDED.boundedExecCircuit_eq_implies_tableau_eq h
  exact boundedExecTableau_same_params_injective M t htab

#print axioms P02.LANE4.AUX.R4_FINAL.tableau_initial_eq_of_whole
#print axioms P02.LANE4.AUX.R4_FINAL.boundedExecTableau_same_params_injective
#print axioms P02.LANE4.AUX.R4_FINAL.boundedExecCircuit_same_params_injective

end R4_FINAL
end AUX
end LANE4
end P02
