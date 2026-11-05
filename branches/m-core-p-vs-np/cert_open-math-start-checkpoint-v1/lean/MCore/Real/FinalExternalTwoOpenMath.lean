import MCore.Real.P01FinalCertificate
import MCore.Real.CookNormalizedG3Contract
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace FinalExternalTwoOpenMath

open CanonicalCircuitBits
open CanonicalSATBoundary
open P01FinalCertificate
open CookNormalizedG3Contract
open FinalExternalCertificate

/-- Exact terminal mathematical payload after all reusable infrastructure is closed.
No proxy endpoint is stored: the P02 field is the concrete failure generator
consumed by FinalExternalInputs itself. -/
structure TwoOpenMathInputs where
  p01 : P01MachineConstruction
  p02 : FailProofAllGaps.FailureGenerator
    (CanonicalSATBoundary.SATBits circuitBitEncoding)

def TwoOpenMathInputs.toFinalExternalInputs
    (I : TwoOpenMathInputs) :
    FinalExternalInputs where
  g1 := construction_closes_p01 ⟨I.p01⟩
  g2 := I.p02
  g3 := cookNormalizedExternalContract

theorem two_open_math_closes_external
    (I : TwoOpenMathInputs) :
    FailProofAllGaps.OfficialPneqNP
      cookNormalizedSelection.model.P
      cookNormalizedSelection.model.NP := by
  exact final_external_certificate I.toFinalExternalInputs

def FinalOpenMathBoundary : Prop :=
  Nonempty TwoOpenMathInputs

theorem final_open_math_boundary_closes
    (h : FinalOpenMathBoundary) :
    FailProofAllGaps.OfficialPneqNP
      cookNormalizedSelection.model.P
      cookNormalizedSelection.model.NP := by
  rcases h with ⟨I⟩
  exact two_open_math_closes_external I

#print axioms MCore.Real.FinalExternalTwoOpenMath.two_open_math_closes_external
#print axioms MCore.Real.FinalExternalTwoOpenMath.final_open_math_boundary_closes

end FinalExternalTwoOpenMath
end Real
end MCore
