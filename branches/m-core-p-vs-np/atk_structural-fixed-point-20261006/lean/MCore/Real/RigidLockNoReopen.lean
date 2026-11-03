import MCore.Real.StructuralNoReopen
import MCore.Real.StructuralDiagonalObstruction

namespace MCore
namespace Real
namespace RigidLockNoReopen

-- Active rigid lock: structural evidence only, never endpoint truth.

open CanonicalFinalProof
open P02TerminalForcingG2
open StructuralNoReopen

inductive GuardClassification where
  | evidenceOfStructuralFixedPoint
  | needsMaterialBreak
  deriving DecidableEq, Repr

structure InfiniteRouteAttempt (P : Prop) where
  Target : Prop
  refinement : GainZero P
  target_eq : refinement.Target = Target
  expandsParams : Bool
  createsLoopShape : Bool
  selfNegatesSyntactically : Bool
  informationGain : Nat

def isGain0Loop
    {P : Prop}
    (R : InfiniteRouteAttempt P) : Bool :=
  R.expandsParams &&
  R.createsLoopShape &&
  R.selfNegatesSyntactically &&
  (R.informationGain == 0)

def rigidLock
    {P : Prop}
    (R : InfiniteRouteAttempt P) : GuardClassification :=
  if isGain0Loop R then
    .evidenceOfStructuralFixedPoint
  else
    .needsMaterialBreak

/--
Every route admitted into the rigid lock already carries a GainZero proof.
Therefore its target is equivalent to P. This is evidence of structural
invariance only; it does not prove P.
-/
theorem rigid_route_target_iff_terminal
    {P : Prop}
    (R : InfiniteRouteAttempt P) :
    R.Target ↔ P := by
  rw [← R.target_eq]
  exact gainZero_fixed_point R.refinement

/--
If the detector marks the attempt as a zero-gain loop, the mathematical
conclusion is still only Target ↔ P.
-/
theorem detected_gain0_is_structural_evidence
    {P : Prop}
    (R : InfiniteRouteAttempt P)
    (_h : isGain0Loop R = true) :
    R.Target ↔ P :=
  rigid_route_target_iff_terminal R

/--
A proposed "smaller theorem" that is itself equivalent to P has not reduced
the terminal obligation.
-/
def equivalent_subtarget_has_zero_terminal_gain
    {P Pmin : Prop}
    (hEq : Pmin ↔ P) :
    GainZero P where
  Target := Pmin
  sound := hEq.mp
  complete := hEq.mpr

/--
No claim is made about all imaginable future subtheorems. The lock rejects
only a proposed subtarget once an equivalence back to P has actually been
proved.
-/
theorem reject_equivalent_minimum
    {P Pmin : Prop}
    (hEq : Pmin ↔ P) :
    (equivalent_subtarget_has_zero_terminal_gain hEq).Target ↔ P :=
  gainZero_fixed_point (equivalent_subtarget_has_zero_terminal_gain hEq)

/--
G2 specialization: the pointwise formulation is permanently classified as
structural evidence, not as a new proof route.
-/
def g2PointwiseRigidAttempt :
    InfiniteRouteAttempt P02TerminalForcingG2.G2_TERMINAL where
  Target := g2PointwiseGainZero.Target
  refinement := g2PointwiseGainZero
  target_eq := rfl
  expandsParams := true
  createsLoopShape := true
  selfNegatesSyntactically := true
  informationGain := 0

theorem g2_pointwise_rigid_evidence :
    g2PointwiseRigidAttempt.Target ↔
      P02TerminalForcingG2.G2_TERMINAL :=
  rigid_route_target_iff_terminal g2PointwiseRigidAttempt

theorem g2_pointwise_rigid_classification :
    rigidLock g2PointwiseRigidAttempt =
      .evidenceOfStructuralFixedPoint := by
  rfl

#print axioms MCore.Real.RigidLockNoReopen.rigid_route_target_iff_terminal
#print axioms MCore.Real.RigidLockNoReopen.detected_gain0_is_structural_evidence
#print axioms MCore.Real.RigidLockNoReopen.reject_equivalent_minimum
#print axioms MCore.Real.RigidLockNoReopen.g2_pointwise_rigid_evidence
#print axioms MCore.Real.RigidLockNoReopen.g2_pointwise_rigid_classification

end RigidLockNoReopen
end Real
end MCore
