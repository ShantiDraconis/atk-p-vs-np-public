import MCore.Real.FinalExternal

namespace MCore.Real

/-- Exact final producer from the two mathematically relevant SAT facts.
    No additional wrapper hypothesis is introduced. -/
def finalExternal_of_sat_inputs
    (hNP : SATInNP)
    (hFail : UniversalSATFailure) :
    FinalExternalCertificate :=
  ⟨{
    satInNP := hNP
    satLowerBound := ⟨hFail⟩
  }⟩

theorem FINAL_ROOT_of_sat_inputs
    (hNP : SATInNP)
    (hFail : UniversalSATFailure) :
    FINAL_ROOT :=
  finalExternalCertificate_to_FINAL_ROOT
    (finalExternal_of_sat_inputs hNP hFail)

#print axioms MCore.Real.finalExternal_of_sat_inputs
#print axioms MCore.Real.FINAL_ROOT_of_sat_inputs

-- ATK exact-final revalidation 2026-10-01
end MCore.Real
