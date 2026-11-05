import P02.LANE4.AUX.R4_INITIAL_INJECTIVE

namespace P02
namespace LANE4
namespace AUX
namespace R4_INITIAL_CNF_DECODER

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding

abbrev ntmSetSymbolClauses_target_injective :=
  R4_INITIAL_INJECTIVE.ntmSetSymbolClauses_target_injective

abbrev ntmInitialCNF_eq_implies_head_eq :=
  R4_INITIAL_INJECTIVE.ntmInitialCNF_eq_implies_head_eq

abbrev ntmInitialCNF_injective_fixed :=
  R4_INITIAL_INJECTIVE.ntmInitialCNF_injective_fixed

theorem initialCNF_source_recovery
    (M : PolyNTMCandidate)
    (t : Nat)
    {x y : BitString}
    (h : ntmInitialCNF M x t = ntmInitialCNF M y t) :
    x = y :=
  R4_INITIAL_INJECTIVE.ntmInitialCNF_injective_fixed M t h

#print axioms P02.LANE4.AUX.R4_INITIAL_CNF_DECODER.initialCNF_source_recovery

end R4_INITIAL_CNF_DECODER
end AUX
end LANE4
end P02
