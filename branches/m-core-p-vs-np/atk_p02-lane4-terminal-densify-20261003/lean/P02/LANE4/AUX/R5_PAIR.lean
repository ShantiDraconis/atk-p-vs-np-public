import P02.LANE4.AUX.R5_PAIR_INJECTIVE

namespace P02
namespace LANE4
namespace AUX
namespace R5_PAIR

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.P02ComplementRunRealization
open MCore.Real.P02TotalCandidateKleeneReduction
open MCore.Real.PNPNTMTableauEncoding

abbrev boundedExecTableau_eq_implies_time_eq :=
  R5_PAIR_INJECTIVE.boundedExecTableau_eq_implies_time_eq

abbrev boundedExecTableau_pair_injective :=
  R5_PAIR_INJECTIVE.boundedExecTableau_pair_injective

abbrev boundedExecCircuit_pair_injective :=
  R5_PAIR_INJECTIVE.boundedExecCircuit_pair_injective

abbrev reduce_M_injective_final :=
  R5_PAIR_INJECTIVE.reduce_M_injective_final

theorem reduction_source_recovery
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    {x y : BitString}
    (h :
      (complementSemanticReduction M hTotal).reduce x =
      (complementSemanticReduction M hTotal).reduce y) :
    x = y :=
  R5_PAIR_INJECTIVE.reduce_M_injective_final M hTotal h

#print axioms P02.LANE4.AUX.R5_PAIR.reduction_source_recovery

end R5_PAIR
end AUX
end LANE4
end P02
