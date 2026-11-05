import Mathlib
import MCore.Real.OpenMathCore.Behavior
import MCore.Real.OpenMathCore.Topology
import MCore.Real.OpenMathCore.Algebra
import MCore.Real.OpenMathCore.T5FBridge

namespace MCore.Real.OpenMathCore

structure AuxiliaryGeometry where
  potential : RealPotential
  topology : TopologicalBehavior

structure OpenMathAuxiliaryBundle where
  behavior : CandidateBehavior
  geometry : AuxiliaryGeometry

/-- Terminal separation is stable under arbitrary replacement of auxiliary
algebra/topology/behavior data because its proof object is carried separately. -/
theorem separation_stable_under_auxiliary_change
    (L : TotalCandidateSeparationLaw)
    (_A _B : OpenMathAuxiliaryBundle) :
    T5FCore := by
  exact separationLaw_implies_T5FCore L

/-- The terminal theorem depends on the separation law, not on a chosen
potential, topology, metric, derivative, or integral representation. -/
theorem terminal_independent_of_auxiliary_bundle
    (h : OpenMathTerminalGap)
    (_A : OpenMathAuxiliaryBundle) :
    T5FCore := by
  exact openMathTerminalGap_implies_T5FCore h

end MCore.Real.OpenMathCore
