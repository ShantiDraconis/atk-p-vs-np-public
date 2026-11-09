import MCore.Real.P03ClosureClasses
import MCore.Real.P03ClosureOperations
import MCore.Real.P03ClosureOperators
import MCore.Real.P03ClosureLaws
import MCore.Real.P03OpenMathFrontier
import MCore.Real.P02AntiModels
import MCore.Real.P03CounterexampleLaws
import MCore.Real.P03TransitionClosure
import MCore.Real.P03TerminalSemanticBridge
import MCore.Real.P03CriticalHalfSymmetry
import MCore.Real.P03PolynomialWitness
import MCore.Real.P03RangeFailureFrontier
import MCore.Real.P03PerfectFlipDichotomy
import MCore.Real.P03UniformRangeDecoder
import MCore.Real.P03PerfectFlipConstruction

namespace MCore
namespace Real
namespace P03ClosureKernel

open P03MaterialLaw
open P03OpenMathFrontier
open P03TerminalSemanticBridge
open P03CriticalHalfSymmetry
open P03PolynomialWitness
open P03RangeFailureFrontier
open P03PerfectFlipDichotomy

/--
The structural kernel is fully decomposed, but the material endpoint remains
fail-closed until CrossOrbitFullInputLaw is inhabited.
-/
theorem fail_closed_status_preserved :
    MATERIAL_GAPS = 1 ∧
    OPEN_BRIDGE = 1 ∧
    GREEN = false := by
  rfl

/-- The single remaining material target exposed by the kernel. -/
abbrev RemainingOpenMath : Prop :=
  FullRunAcceptanceLaw

theorem remaining_open_math_iff_cross_orbit :
    RemainingOpenMath ↔ CrossOrbitFullInputLaw :=
  full_run_acceptance_law_iff_cross_orbit_law

#print axioms MCore.Real.P03ClosureKernel.fail_closed_status_preserved
theorem remaining_open_math_iff_half_symmetry_material_bridge :
    RemainingOpenMath ↔
      Nonempty (HalfSymmetryMaterialBridge canonicalHalfSymmetry) := by
  constructor
  · intro H
    exact
      (materialBridge_iff_fullRunAcceptanceLaw canonicalHalfSymmetry).2 H
  · intro H
    exact
      (materialBridge_iff_fullRunAcceptanceLaw canonicalHalfSymmetry).1 H

#print axioms MCore.Real.P03ClosureKernel.remaining_open_math_iff_cross_orbit
theorem remaining_open_math_iff_polynomial_witness_law :
    RemainingOpenMath ↔ PolynomialWitnessLaw :=
  polynomialWitnessLaw_iff_fullRunAcceptanceLaw.symm

#print axioms MCore.Real.P03ClosureKernel.remaining_open_math_iff_half_symmetry_material_bridge
theorem remaining_open_math_iff_range_failure_law :
    RemainingOpenMath ↔ RangeFailureLaw :=
  rangeFailureLaw_iff_fullRunAcceptanceLaw.symm

#print axioms MCore.Real.P03ClosureKernel.remaining_open_math_iff_polynomial_witness_law
theorem remaining_open_math_iff_not_existsPerfectFlip :
    RemainingOpenMath ↔ ¬ ExistsPerfectFlip := by
  rw [remaining_open_math_iff_range_failure_law]
  constructor
  · intro hRange hFlip
    exact (existsPerfectFlip_iff_not_rangeFailureLaw.mp hFlip) hRange
  · intro hNoFlip
    by_contra hNoRange
    exact hNoFlip
      (existsPerfectFlip_iff_not_rangeFailureLaw.mpr hNoRange)

theorem remaining_open_math_or_existsPerfectFlip :
    RemainingOpenMath ∨ ExistsPerfectFlip := by
  rw [remaining_open_math_iff_range_failure_law]
  exact rangeFailureLaw_or_existsPerfectFlip

#print axioms MCore.Real.P03ClosureKernel.remaining_open_math_iff_range_failure_law
#print axioms MCore.Real.P03ClosureKernel.remaining_open_math_iff_not_existsPerfectFlip
#print axioms MCore.Real.P03ClosureKernel.remaining_open_math_or_existsPerfectFlip

end P03ClosureKernel
end Real
end MCore
