import P02.LANE4.AUX.R4_FINAL

namespace P02
namespace LANE4
namespace AUX
namespace R4_FIXED_FUEL

open MCore
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.PNPNTMTableauEncoding

abbrev tableau_initial_eq_of_whole :=
  R4_FINAL.tableau_initial_eq_of_whole

abbrev boundedExecTableau_injective_final :=
  R4_FINAL.boundedExecTableau_same_params_injective

abbrev boundedExecCircuit_same_params_injective_final :=
  R4_FINAL.boundedExecCircuit_same_params_injective

theorem fixedFuel_source_recovery
    (M : PolyNTMCandidate)
    (t : Nat)
    {x y : BitString}
    (h : boundedExecCircuit_NTM M x t = boundedExecCircuit_NTM M y t) :
    x = y :=
  R4_FINAL.boundedExecCircuit_same_params_injective M t h

#print axioms P02.LANE4.AUX.R4_FIXED_FUEL.fixedFuel_source_recovery

end R4_FIXED_FUEL
end AUX
end LANE4
end P02
