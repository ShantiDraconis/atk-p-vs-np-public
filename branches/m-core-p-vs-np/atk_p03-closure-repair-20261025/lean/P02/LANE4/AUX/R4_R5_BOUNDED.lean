import P02.LANE4.AUX.R2_R4_RADIUS
import P02.LANE4.AUX.R1_R3_REAL
import MCore.Real.PNPNTMTableauEncoding

namespace P02
namespace LANE4
namespace AUX
namespace R4_R5_BOUNDED

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding

/-- Equality of bounded-execution circuits reflects equality of the underlying
tableau CNFs because `boundedExecCircuit_NTM` is exactly `ntmCNFCircuit`
applied to the tableau, and R3c established injectivity of that wrapper. -/
theorem boundedExecCircuit_eq_implies_tableau_eq
    {M : PolyNTMCandidate}
    {x y : BitString}
    {t : Nat}
    (h : boundedExecCircuit_NTM M x t = boundedExecCircuit_NTM M y t) :
    boundedExecTableauCNF_NTM M x t =
      boundedExecTableauCNF_NTM M y t := by
  apply R1_R3_REAL.ntmCNFCircuit_injective
  simpa [boundedExecCircuit_NTM] using h

/-- The final acceptance block depends only on `M,t`, not on the source
bitstring.  Hence equality of whole tableaux implies equality after deleting
that common final singleton block. -/
theorem boundedExecTableau_eq_without_final
    {M : PolyNTMCandidate}
    {x y : BitString}
    {t : Nat}
    (h : boundedExecTableauCNF_NTM M x t =
      boundedExecTableauCNF_NTM M y t) :
    ntmInitialCNF M x t ++ ntmTransitionsCNF M x t =
      ntmInitialCNF M y t ++ ntmTransitionsCNF M y t := by
  have hdrop := congrArg List.dropLast h
  simpa [boundedExecTableauCNF_NTM, ntmFinalAcceptanceCNF,
    List.append_assoc] using hdrop

/-- Circuit equality therefore reaches the exact remaining structural cut:
initial block plus transition block. -/
theorem boundedExecCircuit_eq_without_final
    {M : PolyNTMCandidate}
    {x y : BitString}
    {t : Nat}
    (h : boundedExecCircuit_NTM M x t = boundedExecCircuit_NTM M y t) :
    ntmInitialCNF M x t ++ ntmTransitionsCNF M x t =
      ntmInitialCNF M y t ++ ntmTransitionsCNF M y t :=
  boundedExecTableau_eq_without_final
    (boundedExecCircuit_eq_implies_tableau_eq h)

/-
Remaining AUX cut before R4 can be promoted:

  ntmInitialCNF M x t ++ ntmTransitionsCNF M x t
    =
  ntmInitialCNF M y t ++ ntmTransitionsCNF M y t

  ⟹ ntmInitialCNF M x t = ntmInitialCNF M y t.

This cannot be obtained by prefix cancellation until equality of the initial
prefix lengths (equivalently, equality of ntmRadius at fixed t) has first been
extracted from the whole tableau.  R2_R4_RADIUS already proves that once
initial-block equality is available, radius and source length follow exactly.

No endpoint assumption is introduced here.
-/

#print axioms P02.LANE4.AUX.R4_R5_BOUNDED.boundedExecCircuit_eq_implies_tableau_eq
#print axioms P02.LANE4.AUX.R4_R5_BOUNDED.boundedExecTableau_eq_without_final
#print axioms P02.LANE4.AUX.R4_R5_BOUNDED.boundedExecCircuit_eq_without_final

end R4_R5_BOUNDED
end AUX
end LANE4
end P02
