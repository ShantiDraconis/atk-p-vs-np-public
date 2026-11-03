import MCore.K10
import MCore.Real.P01FinalCertificate
import MCore.Real.FinalProofAttack

/-!
# Integrated material proof boundary

This module combines already proved implications and exposes their exact
assumptions. It deliberately does not assert an inhabitant of either open
material producer and does not equate an arbitrary-encoder model with the
standard polynomial-time complexity classes.
-/

namespace MCore
namespace Real
namespace IntegratedMaterialProofs

/-- An actual P01 machine construction yields the canonical SAT machine closure. -/
theorem p01_of_material_machine
    (C : P01FinalCertificate.P01MachineConstruction) :
    CanonicalSATMachineClosure :=
  P01FinalCertificate.construction_closes_p01 ⟨C⟩

/-- An actual separation witness proves a class separation in its supplied model. -/
theorem separation_of_material_witness
    {Language α Value : Type}
    (W : SeparationWitnessData Language α Value) :
    ¬ (∀ L, W.interface.classical.inP L ↔ W.interface.classical.inNP L) :=
  separation_witness_separates W

/-- The existing arbitrary-encoder model cannot establish its SAT lower bound. -/
theorem arbitrary_encoder_sat_lower_bound_impossible :
    ¬ FinalProofAttack.SATLowerBoundCertificate :=
  FinalProofAttack.current_SATLowerBoundCertificate_refuted

#print axioms MCore.Real.IntegratedMaterialProofs.p01_of_material_machine
#print axioms MCore.Real.IntegratedMaterialProofs.separation_of_material_witness
#print axioms MCore.Real.IntegratedMaterialProofs.arbitrary_encoder_sat_lower_bound_impossible

end IntegratedMaterialProofs
end Real
end MCore
